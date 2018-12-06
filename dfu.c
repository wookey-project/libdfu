#include "autoconf.h"
#include "api/types.h"
#include "api/syscall.h"
#include "api/print.h"
#include "api/dfu.h"
#include "usb.h"
#include "dfu_desc.h"
#if 0
#include "dummy_crypt.h"
#include "dummy_flash.h"
#include "stm32f4xx.h"
#include "stm32f4xx_nvic.h"
#include "cortex_m4_systick.h"
#endif
#include "usb_control.h"
#include "queue.h"

#define USB_DFU_DEBUG 1

/* FIXME: should be get back from USB driver */
#define MAX_TIME_DETACH     4000

/* FIXME dummy */
uint8_t read_firmware_data_cmd = 0;
uint8_t read_firmware_data_done = 0;

/*
 * Association between a request and a transition to a next state. This couple
 * depend on the current state and is use in the following structure
 */
typedef struct dfu_request_transition {
    uint8_t    request;
    uint8_t    target_state;
} dfu_request_transition_t;

/*
 * all allowed transitions and target states for each current state
 * empty fields are set as 0xff/0xff for request/state couple, which is
 * an inexistent state and request
 */
static const struct {
    dfu_state_enum_t          state;
    dfu_request_transition_t  req_trans[5];
} dfu_automaton[] = {
    { APPIDLE,               {
                                 {USB_RQST_DFU_DETACH,APPDETACH},
                                 {USB_RQST_DFU_GET_STATUS,APPIDLE},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff}
                             }
    },
    { APPDETACH,             {
                                 {USB_RQST_DFU_GET_STATUS,APPDETACH},
                                 {USB_RQST_DFU_GET_STATUS,APPDETACH},
                                 {0xff,0xff}, /* also detach timeout and USB reset */
                                 {0xff,0xff},
                                 {0xff,0xff}
                             }
    },
    { DFUIDLE,               {
                                 {USB_RQST_DFU_DNLOAD,DFUDNLOAD_SYNC},
                                 {USB_RQST_DFU_UPLOAD,DFUUPLOAD_IDLE},
                                 {USB_RQST_DFU_ABORT,DFUIDLE},
                                 {USB_RQST_DFU_GET_STATUS,DFUIDLE},
                                 {USB_RQST_DFU_GET_STATE,DFUIDLE}
                             }
    },
    { DFUDNLOAD_SYNC,        {
                                 {USB_RQST_DFU_GET_STATUS,0xff}, /* target state depends on more infos*/
                                 {USB_RQST_DFU_ABORT,DFUIDLE},
                                 {USB_RQST_DFU_GET_STATE,DFUDNLOAD_SYNC},
                                 {0xff,0xff},
                                 {0xff,0xff}
                             }
    },
    { DFUDNBUSY,             {
                                 {0xff,0xff}, /* leave only on timeout */
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff}
                             }
    },
    { DFUDNLOAD_IDLE,        {
                                 {USB_RQST_DFU_DNLOAD,0xff}, /* target state depends on more infos*/
                                 {USB_RQST_DFU_ABORT,DFUIDLE},
                                 {USB_RQST_DFU_GET_STATUS,DFUDNLOAD_IDLE},
                                 {USB_RQST_DFU_GET_STATE,DFUDNLOAD_IDLE},
                                 {0xff,0xff}
                             }
    },
    { DFUMANIFEST_SYNC,      {
                                 {USB_RQST_DFU_GET_STATUS,0xff}, /* target state depends on more infos*/
                                 {USB_RQST_DFU_ABORT,DFUIDLE},
                                 {USB_RQST_DFU_GET_STATE,DFUMANIFEST_SYNC},
                                 {0xff,0xff},
                                 {0xff,0xff}
                             }
    },
    { DFUMANIFEST,           {
                                 {0xff,0xff}, /* only poll timeout */
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff}
                             }
    },
    { DFUMANIFEST_WAIT_RESET,{
                                 {0xff,0xff}, /* infinite loop, waiting for USB reset */
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff}
                             }
    },
    { DFUUPLOAD_IDLE,        {
                                 {USB_RQST_DFU_UPLOAD,0xff}, /* depends (short frame or not) */
                                 {USB_RQST_DFU_ABORT,DFUIDLE},
                                 {USB_RQST_DFU_GET_STATUS,DFUUPLOAD_IDLE},
                                 {USB_RQST_DFU_GET_STATE,DFUUPLOAD_IDLE},
                                 {0xff,0xff}
                             }
    },
    { DFUERROR,              {
                                 {USB_RQST_DFU_CLEAR_STATUS,DFUIDLE},
                                 {USB_RQST_DFU_GET_STATUS,DFUERROR},
                                 {USB_RQST_DFU_GET_STATE,DFUERROR},
                                 {0xff,0xff},
                                 {0xff,0xff}
                             }
    },
};

/*
 * Return the next automaton state, depending on the current state
 * and the current request
 */
static uint8_t dfu_next_state(dfu_state_enum_t  current_state,
        dfu_request_t    request)
{
    for (uint8_t i = 0; i < 5; ++i) {
        if (dfu_automaton[current_state].req_trans[i].request == request) {
            return (dfu_automaton[current_state].req_trans[i].target_state);
        }
    }
    /* fallback, no corresponding request found for  this state */
    return 0xff;
}

/*
 * Is the current request valid for the current state ?
 * DFU standard 1.1 state automaton (Figure A.1, p.28)
 */
static bool dfu_is_valid_transition(dfu_state_enum_t current_state,
        dfu_request_t    request)
{
    for (uint8_t i = 0; i < 5; ++i) {
        if (dfu_automaton[current_state].req_trans[i].request == request) {
            return true;
        }
    }
    /*
     * Didn't find any request associated to current state. This is not a
     * valid transition. We should fallback to DFUERROR state.
     */
    return false;
}

static inline void enter_critical_section(void)
{
    uint8_t ret;
    ret = sys_lock (LOCK_ENTER); /* Enter in critical section */
    if(ret != SYS_E_DONE){
        printf("Error: failed entering critical section!\n");
    }
    return;
}

static inline void leave_critical_section(void)
{
    uint8_t ret;
    ret = sys_lock (LOCK_EXIT);  /* Exit from critical section */
    if(ret != SYS_E_DONE){
        printf("Error: failed exiting critical section!\n");
    }
    return;
}

static volatile const dfu_functional_descriptor_t dfu_fct_desc = {
    .bLength = 0x09,
    .bDescriptorType = 0x21,
    .bmAttributes.bitWillDetach = 0,
    .bmAttributes.bitManifestationTolerant = 1,
#ifdef DEBUG_LVL
    .bmAttributes.bitCanUpload = 1,
#else
    .bmAttributes.bitCanUpload = 0,
#endif
    .bmAttributes.bitCanDnload = 1,
    .wDetachTimeOut = MAX_TIME_DETACH,
    .wTransferSize = MAX_TRANSFERT_SIZE,
    .bcdDFUVersion = 0x0101
};

//#define NOT_TIMER5

static volatile uint8_t data_buffer[MAX_TRANSFERT_SIZE];

static volatile dfu_context_t dfu_context = {0};




static volatile dfu_context_t * const dfu_ctx = &dfu_context;


typedef struct {
    uint16_t id;
    uint32_t size;
    uint8_t * data;
} dfu_data_block_t;

/**********************************************
 * DFU getters
 *********************************************/

uint32_t dfu_get_poll_timeout(void){
    return dfu_ctx->poll_timeout_ms;
}


static inline uint8_t dfu_get_state() {
    return dfu_ctx->state;
}


static inline void dfu_set_status(const dfu_status_enum_t new_status) {
    dfu_ctx->status = new_status;
}


static inline uint8_t dfu_get_status() {
    //printf("\n");
    return dfu_ctx->status;
}

uint8_t dfu_get_status_string_id() {
    return 0;
}

/***********************************************/
static inline void dfu_set_state(const uint8_t new_state)
{
    if (new_state == 0xff) {
        printf("PANIC! this should never arrise !");
        while (1) {};
        return;
    }
    //    printf("%x => %x\n", dfu_ctx->state, new_state);
    dfu_ctx->state = new_state;
}


static void dfu_prepare_stall(void)
{
    usb_driver_stall_out(0);
}

static inline void dfu_error(const dfu_status_enum_t new_status)
{
#if USB_DFU_DEBUG
    printf("%s: status=%d\n", __func__, new_status);
#endif
    if(new_status == ERRSTALLEDPKT){
#if USB_DFU_DEBUG
        printf("stalling...\n");
#endif
        dfu_prepare_stall();
        dfu_set_status(new_status);
        return;
    }
#if USB_DFU_DEBUG
    printf("state -> Error\n");
#endif
    dfu_set_status(new_status);
}

/***********************************************/




static void dfu_release_block(dfu_data_block_t *b)
{
    if(b != NULL){
        if(b->data != NULL){
#ifdef CONFIG_STD_MALLOC_LIGHT
            enter_critical_section();
            wfree((void**)&b->data);
            leave_critical_section();
#endif
        }

#ifdef CONFIG_STD_MALLOC_LIGHT
        enter_critical_section();
        wfree((void**)&b);
        leave_critical_section();
#endif
    }
    b = NULL;
}



static void dfu_functional_desc_request_handler(uint16_t wLength)
{
    //aprintf("functional desc requested, wlength=%d\n", wLength);
    if ( wLength == 0 ){
        usb_driver_setup_send_status(0);
        usb_driver_setup_read_status();
        return;
    }

    if ( wLength >  dfu_fct_desc.bLength) {
        usb_driver_setup_send((uint8_t *)&dfu_fct_desc, dfu_fct_desc.bLength,0);
    }else{
        usb_driver_setup_send((uint8_t *)&dfu_fct_desc, wLength,0);
    }

    usb_driver_setup_read_status();
}


static uint8_t dfu_validate_suffix(dfu_suffix_t * dfu_suffix __attribute__((unused)))
{
    return 1;
}


static uint8_t dfu_validate_sec_suffix(dfu_sec_metadata_hdr_t * dfu_sec_metadata_hdr __attribute__((unused)))
{
    return 1;
}


static uint8_t dfu_validate_memory_policy(uint32_t addr __attribute__((unused)),
        uint32_t length __attribute__((unused)))
{
    //printf("\n");
    return 1;
}

void dfu_set_poll_timeout(uint32_t t)
{

    uint64_t ms;
    uint8_t ret;

#if USB_DFU_DEBUG
    printf("setting poll_timeout_ms to %d\n", t);
#endif
    dfu_ctx->poll_timeout_ms = t;
    ret = sys_get_systick(&ms, PREC_MILLI);
    if (ret != SYS_E_DONE) {
        printf("Error: unable to get systick value !\n");
    }
    dfu_ctx->poll_start = ms;

}


/**********************************************
 * Handlers for each request
 *********************************************/

void dfu_request_detach(struct usb_setup_packet *setup_packet)
{
    /* Sanity check and next state detection */
    uint8_t next_state;
    if (!dfu_is_valid_transition(dfu_get_state(), setup_packet->bRequest)) {
        goto invalid_transition;
    }
    next_state = dfu_next_state(dfu_get_state(), setup_packet->bRequest);

    if (next_state != 0xff) {
        dfu_set_state(next_state);
    } else {
        goto invalid_transition;
    }

    /* effective transition execution (if needed) */
#if 0
    if( (setup_packet->wLength == 0) && (setup_packet->wValue <= dfu_ctx->detach_timeout_ms) ) {
        /* The Detach request is not meaningful in our case.
         * The DFU mode is started by after system reset depending on
         * the boot mode configuration settings, which means that no other
         * application is running at that time.
         */
        dfu_set_state(APPDETACH);
    } else {
        dfu_error(ERRUNKNOWN);
    }
#endif
    return;

invalid_transition:
    dfu_error(ERRUNKNOWN);
    return;

}


void dfu_request_dnload(struct usb_setup_packet *setup_packet)
{
    /* Sanity check and next state detection */
    uint8_t next_state;
    if (!dfu_is_valid_transition(dfu_get_state(), setup_packet->bRequest)) {
        goto invalid_transition;
    }
    next_state = dfu_next_state(dfu_get_state(), setup_packet->bRequest);


    /* effective transition execution (if needed) */
    switch (dfu_get_state()) {
        case DFUIDLE:
            {
                if (   dfu_fct_desc.bmAttributes.bitCanDnload != 1
                        || setup_packet->wLength                  == 0)
                {
                    goto download_not_supported;
                }
                if (setup_packet->wLength > MAX_TRANSFERT_SIZE) {
                    dfu_ctx->block_in_progress = 0;
                    goto size_too_big;
                } else {
                    /* dfu_ctx->data_out_current_block_nb;
                     * FIXME: this should be set to something */
                    dfu_ctx->data_out_nb_blocks = setup_packet->wValue;
                    dfu_ctx->data_out_length = setup_packet->wLength;
                    dfu_set_state(DFUDNLOAD_SYNC); /* We have data to dl */
                    dfu_ctx->block_in_progress = 1;
                    usb_driver_setup_send_status(0);
                    dfu_ctx->block_size = setup_packet->wLength;
                    dfu_ctx->session_in_progress = 1;
#if USB_DFU_DEBUG
                    printf("read %dB\n", dfu_ctx->block_size);
#endif
                    usb_driver_setup_read(dfu_ctx->data_out_buffer, dfu_ctx->block_size,0);
                }
                /* This is a new download session (i.e. new file) */
                dfu_set_state(next_state);
                break;
            }
        case DFUDNLOAD_IDLE:
            {
                /* This is a continuation (next block) of a previously
                 * started file
                 */
                if (setup_packet->wLength == 0) {
                    /* No data => end of transfert */
                    dfu_ctx->data_out_nb_blocks = 0;
                    dfu_ctx->data_out_length = 0;
                    dfu_ctx->data_out_current_block_nb = 0;
                    dfu_ctx->block_in_progress = 0;
                    dfu_set_state(DFUMANIFEST_SYNC);
                    usb_driver_setup_send_status(0);
                } else if (setup_packet->wLength > MAX_TRANSFERT_SIZE) {
                    dfu_ctx->block_in_progress = 0;
                    goto size_too_big;
                } else {
                    /* dfu_ctx->data_out_current_block_nb;
                     * FIXME: this should be set to something */
                    dfu_ctx->data_out_nb_blocks = setup_packet->wValue;
                    dfu_ctx->data_out_length = setup_packet->wLength;
                    dfu_set_state(DFUDNLOAD_SYNC); /* We have data to dl */
                    dfu_ctx->block_in_progress = 1;
                    usb_driver_setup_send_status(0);
                    dfu_ctx->block_size = setup_packet->wLength;
#if USB_DFU_DEBUG
                    printf("read %dB\n", dfu_ctx->block_size);
#endif
                    usb_driver_setup_read(dfu_ctx->data_out_buffer, dfu_ctx->block_size,0);
                }
                break;
            }
        default:
            printf("maybe a missing state: check automaton\n");
            break;
    }

    return;

invalid_transition:
    dfu_error(ERRUNKNOWN);
    return;

    /* FIXME proper error ?*/
download_not_supported:
    printf("dfu error: idle and can't download !\n");
    dfu_error(ERRUNKNOWN);
    return;

size_too_big:
    printf("dfu error ! input size too big!\n");
    dfu_error(ERRSTALLEDPKT);
    return;
}


void dfu_request_upload(struct usb_setup_packet *setup_packet) 
{
    /* Sanity check and next state detection */
    uint8_t next_state;
    if (!dfu_is_valid_transition(dfu_get_state(), setup_packet->bRequest)) {
        goto invalid_transition;
    }
    next_state = dfu_next_state(dfu_get_state(), setup_packet->bRequest);


    /* effective transition execution (if needed) */

    switch (dfu_get_state()) {
        case DFUUPLOAD_IDLE:
            {
                if (setup_packet->wLength == 0) {
                    /* short frame: go back to DFUIDLE */
                    dfu_ctx->data_in_nb_blocks = 0;
                    dfu_ctx->data_in_length = 0;
                    dfu_ctx->data_in_current_block_nb = 0;
                    dfu_ctx->block_in_progress = 0;
                    dfu_ctx->session_in_progress = 0;
                    dfu_set_state(DFUIDLE);
                    /* FIXME: should be botoom-halfed in main thread */
                    usb_driver_setup_send_status(0);
                } else {
                    /* just stay in current state, managing upload */
                    if (setup_packet->wLength > MAX_TRANSFERT_SIZE) {
                        goto size_too_big;
                    } else {
                        read_firmware_data_cmd = 1;
                    }
                }
                break;
            }
        case DFUIDLE:
            {
                if (dfu_fct_desc.bmAttributes.bitCanUpload != 1)
                {
                    goto upload_not_supported;
                }
                dfu_ctx->session_in_progress = 1;
                dfu_set_state(next_state);
                break;
            }
        default:
            printf("maybe a missing state: check automaton\n");
            break;
    }

    return;

invalid_transition:
    dfu_error(ERRUNKNOWN);
    return;

    /* FIXME proper error ?*/
upload_not_supported:
    printf("dfu error ! idle mode and can't upload\n");
    dfu_error(ERRUNKNOWN);
    return;

size_too_big:
    printf("dfu error ! input size too big!\n");
    dfu_error(ERRSTALLEDPKT);
    return;

}

void dfu_request_getstatus(struct usb_setup_packet *setup_packet)
{
    /* Sanity check and next state detection */
    uint8_t next_state;
    device_dfu_status_t status;
    memset((void*)&status, 0, sizeof(device_dfu_status_t));
    if (!dfu_is_valid_transition(dfu_get_state(), setup_packet->bRequest)) {
        goto invalid_transition;
    }
    next_state = dfu_next_state(dfu_get_state(), setup_packet->bRequest);


    /* effective transition execution (if needed) */
    switch( dfu_get_state()) {
        case APPIDLE:
            {
                /* staying in APPIDLE */
                status.bStatus = dfu_get_status();
                status.bState = dfu_get_state();
                status.iString = dfu_get_status_string_id();

                usb_driver_setup_send((void*)&status, sizeof(status),0);
                usb_driver_setup_read_status();
                break;
            }
        case APPDETACH:
            {
                /* staying in APPDETACH */
                status.bStatus = dfu_get_status();
                status.bState = dfu_get_state();
                status.iString = dfu_get_status_string_id();

                usb_driver_setup_send((void*)&status, sizeof(status),0);
                usb_driver_setup_read_status();
                break;
            }
        case DFUIDLE:
            {
                /* staying in DFUIDLE */
                status.bStatus = dfu_get_status();
                status.bState = dfu_get_state();
                status.bwPollTimeout[0] = (dfu_get_poll_timeout() >>  0) & 0xFF;
                status.bwPollTimeout[1] = (dfu_get_poll_timeout() >>  8) & 0xFF;
                status.bwPollTimeout[2] = (dfu_get_poll_timeout() >> 16) & 0xFF;
                status.iString = dfu_get_status_string_id();

                usb_driver_setup_send((void*)&status, sizeof(status),0);
                usb_driver_setup_read_status();
                break;
            }
        case DFUDNLOAD_SYNC:
            {
                if (dfu_ctx->block_in_progress == 1) {
                    /* Block transfert still in progress */
                    dfu_set_poll_timeout(MAX_POLL_TIMEOUT);
                    dfu_set_state(DFUDNBUSY);
                } else {
                    dfu_set_state(DFUDNLOAD_IDLE);
                }
                status.bStatus = dfu_get_status();
                status.bState = dfu_get_state();
                status.bwPollTimeout[0] = (dfu_get_poll_timeout() >>  0) & 0xFF;
                status.bwPollTimeout[1] = (dfu_get_poll_timeout() >>  8) & 0xFF;
                status.bwPollTimeout[2] = (dfu_get_poll_timeout() >> 16) & 0xFF;
                status.iString = dfu_get_status_string_id();

                usb_driver_setup_send((void*)&status, sizeof(status),0);
                usb_driver_setup_read_status();
                break;
            }
        case DFUDNLOAD_IDLE:
            {
                status.bStatus = dfu_get_status();
                status.bState = dfu_get_state();
                status.bwPollTimeout[0] = (dfu_get_poll_timeout() >>  0) & 0xFF;
                status.bwPollTimeout[1] = (dfu_get_poll_timeout() >>  8) & 0xFF;
                status.bwPollTimeout[2] = (dfu_get_poll_timeout() >> 16) & 0xFF;
                status.iString = dfu_get_status_string_id();

                usb_driver_setup_send((void*)&status, sizeof(status),0);
                usb_driver_setup_read_status();
                break;
            }
        case DFUMANIFEST_SYNC:
            {
                /* INFO: we consider here that manifestation is always complete,
                 * i.e. never in progress as we don't have enought RAM to
                 * buffer multiple blocks before flushing in mass storage
                 * at the end of manifestation.
                 * The manifestation complete status bit is not implemented.
                 */
                dfu_ctx->session_in_progress = 0;
                dfu_set_state(DFUIDLE);

                status.bStatus = dfu_get_status();
                status.bState = dfu_get_state();
                status.bwPollTimeout[0] = (dfu_get_poll_timeout() >>  0) & 0xFF;
                status.bwPollTimeout[1] = (dfu_get_poll_timeout() >>  8) & 0xFF;
                status.bwPollTimeout[2] = (dfu_get_poll_timeout() >> 16) & 0xFF;
                status.iString = dfu_get_status_string_id();

                usb_driver_setup_send((void*)&status, sizeof(status),0);
                usb_driver_setup_read_status();
                break;
            }
        case DFUUPLOAD_IDLE:
            {
                /* stays in DFUUPLOAD_IDLE */
                status.bStatus = dfu_get_status();
                status.bState = dfu_get_state();
                status.bwPollTimeout[0] = (dfu_get_poll_timeout() >>  0) & 0xFF;
                status.bwPollTimeout[1] = (dfu_get_poll_timeout() >>  8) & 0xFF;
                status.bwPollTimeout[2] = (dfu_get_poll_timeout() >> 16) & 0xFF;
                status.iString = dfu_get_status_string_id();

                usb_driver_setup_send((void*)&status, sizeof(status),0);
                usb_driver_setup_read_status();
                break;
            }
        case DFUERROR:
            {
                /* stays in DFUERROR */
                status.bStatus = dfu_get_status();
                status.bState = dfu_get_state();
                status.bwPollTimeout[0] = (dfu_get_poll_timeout() >>  0) & 0xFF;
                status.bwPollTimeout[1] = (dfu_get_poll_timeout() >>  8) & 0xFF;
                status.bwPollTimeout[2] = (dfu_get_poll_timeout() >> 16) & 0xFF;
                status.iString = dfu_get_status_string_id();

                usb_driver_setup_send((void*)&status, sizeof(status),0);
                usb_driver_setup_read_status();
                break;
            }
        default:
            printf("maybe a missing state: check automaton\n");
            break;
    }
    return;

invalid_transition:
    dfu_error(ERRUNKNOWN);
    return;
}

void dfu_request_clrstatus(struct usb_setup_packet *setup_packet) 
{
    /* Sanity check and next state detection */
    uint8_t next_state;
    device_dfu_status_t status;
    memset((void*)&status, 0, sizeof(device_dfu_status_t));
    if (!dfu_is_valid_transition(dfu_get_state(), setup_packet->bRequest)) {
        goto invalid_transition;
    }
    next_state = dfu_next_state(dfu_get_state(), setup_packet->bRequest);

    /* effective transition execution (if needed) */
    dfu_init_context();
    dfu_set_state(next_state);
    usb_driver_setup_send_status(0);
    return;

invalid_transition:
    dfu_error(ERRUNKNOWN);
    return;
}

void dfu_request_getstate(struct usb_setup_packet *setup_packet) 
{
    /* Sanity check and next state detection */
    uint8_t next_state;
    device_dfu_status_t status;
    memset((void*)&status, 0, sizeof(device_dfu_status_t));
    if (!dfu_is_valid_transition(dfu_get_state(), setup_packet->bRequest)) {
        goto invalid_transition;
    }
    next_state = dfu_next_state(dfu_get_state(), setup_packet->bRequest);

    /* effective transition execution (if needed) */
    switch( dfu_get_state()) {
        case APPIDLE:
        case APPDETACH:
        case DFUIDLE:
        case DFUDNLOAD_SYNC:
        case DFUDNLOAD_IDLE:
        case DFUMANIFEST_SYNC:
        case DFUUPLOAD_IDLE:
        case DFUERROR:
            {
                uint8_t state = dfu_get_state();

                usb_driver_setup_send((void*)&state, 1, 0);
                usb_driver_setup_read_status();
                break;
            }
        default:
            printf("maybe a missing state: check automaton\n");
            break;
    }
    return;

invalid_transition:
    dfu_error(ERRUNKNOWN);
    return;
}

void dfu_request_abort(struct usb_setup_packet *setup_packet) 
{
    /* Sanity check and next state detection */
    uint8_t next_state;
    device_dfu_status_t status;
    memset((void*)&status, 0, sizeof(device_dfu_status_t));
    if (!dfu_is_valid_transition(dfu_get_state(), setup_packet->bRequest)) {
        goto invalid_transition;
    }
    next_state = dfu_next_state(dfu_get_state(), setup_packet->bRequest);

    /* effective transition execution (if needed) */
    switch( dfu_get_state()) {
        case DFUIDLE:
        case DFUDNLOAD_SYNC:
        case DFUDNLOAD_IDLE:
        case DFUMANIFEST_SYNC:
        case DFUUPLOAD_IDLE:
            {
                /* effective transition execution (if needed) */
                dfu_init_context();
                dfu_set_state(next_state);
                usb_driver_setup_send_status(0);
                break;
            }
        default:
            printf("maybe a missing state: check automaton\n");
            break;

    }
    return;

invalid_transition:
    dfu_error(ERRUNKNOWN);
    return;
}


/*******************************************************
 * End of request logics functions
 ******************************************************/

/* request node, to be enqueue in handler mode, dequeue in main thread */
typedef struct {
    dfu_request_t            request;
    struct usb_setup_packet  setup_packet;
} request_queue_node_t;

#if USB_DFU_DEBUG
static const char *request_name[] = {
    "USB_RQST_DFU_DETACH",
    "USB_RQST_DFU_DNLOAD",
    "USB_RQST_DFU_UPLOAD",
    "USB_RQST_DFU_GET_STATUS",
    "USB_RQST_DFU_CLEAR_STATUS",
    "USB_RQST_DFU_GET_STATE",
    "USB_RQST_DFU_ABORT"
};
#endif

static volatile  request_queue_node_t *current_dfu_cmd = NULL;
struct queue *dfu_cmd_queue = NULL;
static volatile unsigned int dfu_cmd_queue_empty = 1;

static volatile bool dfu_data_to_store = 0;


static void dfu_release_current_dfu_cmd(void)
{
    if (current_dfu_cmd != NULL) {
        enter_critical_section();
        if (wfree((void**)&current_dfu_cmd)) {
            while(1){};
        }
        leave_critical_section();
    }
    current_dfu_cmd = NULL;
    return;
}



/******************************************************
 * Global root handler dispatcher (handler mode)
 *****************************************************/
static void dfu_class_parse_request(struct usb_setup_packet *setup_packet)
{
    uint8_t ret;
    request_queue_node_t *cur_req = 0;

    if (setup_packet->bRequest > USB_RQST_DFU_ABORT) {
#if USB_DFU_DEBUG
        aprintf("dfu: %s: unknown request\n", __func__);
#endif
        dfu_error(ERRUNKNOWN);
        return;
    }

#if USB_DFU_DEBUG
    aprintf("[handler mode] ENQUEUINQ => state %d, req %d\n", dfu_get_state(), setup_packet->bRequest);
#endif
    ret = wmalloc((void**)&cur_req, sizeof(request_queue_node_t), ALLOC_NORMAL);
    if(ret){
        aprintf("Error while allocating queue !!!\n");
        while(1){};
    }

#if USB_DFU_DEBUG
    aprintf("req: %s\n", request_name[setup_packet->bRequest]);
#endif
    cur_req->request = setup_packet->bRequest;
    memcpy((void*)&cur_req->setup_packet, setup_packet, sizeof(struct usb_setup_packet));
    queue_enqueue(dfu_cmd_queue, cur_req);
    dfu_cmd_queue_empty = 0;

    return;
}


/******************************************************
 * Global root request executor (main thread)
 *****************************************************/
static void dfu_class_execute_request(void)
{
    if(dfu_cmd_queue_empty == 1)
    {
        return;
    }
    enter_critical_section();
    current_dfu_cmd = queue_dequeue(dfu_cmd_queue);
    if(queue_is_empty(dfu_cmd_queue)) {
        dfu_cmd_queue_empty = 1;
    }
    leave_critical_section();
#if USB_DFU_DEBUG
    printf("[main thread] DEQUEUING\n");
#endif
    switch( current_dfu_cmd->setup_packet.bRequest ) {
        case USB_RQST_DFU_DETACH:
#if USB_DFU_DEBUG
            printf("DFU_DETACH\n");
#endif
            dfu_request_detach((struct usb_setup_packet*)&current_dfu_cmd->setup_packet);
            break;

        case USB_RQST_DFU_DNLOAD:
#if USB_DFU_DEBUG
            printf("DFU_DNLOAD\n");
#endif
            dfu_request_dnload((struct usb_setup_packet*)&current_dfu_cmd->setup_packet);
            break;

        case USB_RQST_DFU_UPLOAD:
#if USB_DFU_DEBUG
            printf("DFU_UPLOAD\n");
#endif
            dfu_request_upload((struct usb_setup_packet*)&current_dfu_cmd->setup_packet);
            break;

        case USB_RQST_DFU_GET_STATUS:
#if USB_DFU_DEBUG
            printf("DFU_GET_STATUS\n");
#endif
            dfu_request_getstatus((struct usb_setup_packet*)&current_dfu_cmd->setup_packet);
            break;

        case USB_RQST_DFU_CLEAR_STATUS:
#if USB_DFU_DEBUG
            printf("DFU_CLEAR_STATUS\n");
#endif
            dfu_request_clrstatus((struct usb_setup_packet*)&current_dfu_cmd->setup_packet);
            break;

        case USB_RQST_DFU_GET_STATE:
#if USB_DFU_DEBUG
            printf("DFU_GET_STATE\n");
#endif
            dfu_request_getstate((struct usb_setup_packet*)&current_dfu_cmd->setup_packet);
            break;

        case USB_RQST_DFU_ABORT:
#if USB_DFU_DEBUG
            printf("DFU_GET_ABORT\n");
#endif
            dfu_request_abort((struct usb_setup_packet*)&current_dfu_cmd->setup_packet);
            break;

#ifdef DEBUG_LVL // FIXME We should implement these features
        case USB_RQST_DFU_DEBUG_CHKSIGN:
        case USB_RQST_DFU_DEBUG_DECRYPT:
        case USB_RQST_DFU_DEBUG_CRYPT:

        case USB_RQST_DFU_DEBUG_GETADDR:
        case USB_RQST_DFU_DEBUG_SETSIZE:
        case USB_RQST_DFU_DEBUG_GETSIZE:
#endif
        default:
            printf("dfu: %s: unknown request\n", __func__);
            dfu_error(ERRUNKNOWN);
    }
    /* FIXME: current dfu cmd does not need to be global */
    dfu_release_current_dfu_cmd();
}


/*
 * The USB content as been read into local buffer and is waiting to be stored
 * into the flash. This function does this
 */
static void dfu_store_data(void)
{
#if USB_DFU_DEBUG
    printf("storing data...\n");
#endif
    if (dfu_get_state() != DFUDNBUSY) {
        printf("Error! storing data in %d mode !", dfu_get_state());
        dfu_error(ERRUNKNOWN);
        return;
    }
    // FIXME: simulate the IPCs and write access by now...

    // now set the write action as done
    dfu_ctx->data_out_current_block_nb += 1;
    dfu_ctx->block_in_progress = 0;
    dfu_ctx->poll_start = 0;
    dfu_data_to_store = 0;
    /* INFO: we consider that even if the poll timeout is not finished, we go
     * back to DNLOAD_SYNC state
     * FIXME: if we want to be paranoid, we should effecively wait for the
     * residual timeout before changing current state
     */
    dfu_set_state(DFUDNLOAD_SYNC);
    return;
}


static void dfu_data_out_handler(uint32_t size __attribute__((unused)))
{
#if USB_DFU_DEBUG
    aprintf("end of USB read\n");
#endif
    /* all data received from host. This handler is executed by the lower
     * USB stack at the end of the effective usb_status_read() call.
     * Here, we set a flag to request the main thread to effetively copy the
     * buffer content into the flash. When this is done, the flag is
     * lowered and the block_in_pogress field of the dfu context is set to 0.
     */
    dfu_data_to_store = 1;
}


static void dfu_data_in_handler(void)
{
    if (dfu_ctx->block_in_progress == 1)
    {
        dfu_ctx->block_in_progress = 0;
    }
}


/****************************************************
 * DFU main loop
 **************************************************/

void dfu_loop(void)
{
    while(1){
#if USB_DFU_DEBUG
	    aprintf_flush();
#endif
	    /* storing data and go out of DNBUSY bottom half */
	    if (dfu_data_to_store) {
        	dfu_store_data();
	    }
#if USB_DFU_DEBUG
	    aprintf_flush();
#endif
	    /* all DFU automaton execution */
	    dfu_class_execute_request();
#if USB_DFU_DEBUG
	    aprintf_flush();
#endif
    }
}


/****************************************************
 * Init functions
 **************************************************/

void dfu_init_context(void)
{
    dfu_context.block_in_progress = 0;
    dfu_context.session_in_progress = 0;
    dfu_context.status = OK;
    dfu_context.state = DFUIDLE;
    dfu_context.data_out_buffer = (uint8_t**)&data_buffer;
    dfu_context.data_out_current_block_nb = 0;
    dfu_context.data_out_nb_blocks = 0;
    dfu_context.data_out_length = 0;
    dfu_context.data_in_buffer = (uint8_t**)&data_buffer;
    dfu_context.data_in_nb_blocks = 0;
    dfu_context.data_in_current_block_nb = 0;
    dfu_context.data_in_length = 0;
    dfu_context.flash_address = 0x80000000;
    dfu_context.detach_timeout_ms = MAX_TIME_DETACH;
    dfu_context.detach_timeout_start = 0;
    dfu_context.poll_timeout_ms = MAX_POLL_TIMEOUT;
    dfu_context.poll_start = 0;
    dfu_context.block_size = MAX_TRANSFERT_SIZE;
    dfu_context.firmware_size = 0;
    dfu_context.current_block_offset = 0;
}


void dfu_early_init(void)
{
    usb_driver_early_init(dfu_data_out_handler, dfu_data_in_handler);
}


void dfu_init(void)
{

    usb_driver_map();
#ifdef CONFIG_STD_MALLOC_LIGHT
    wmalloc_init();

    dfu_cmd_queue = queue_create(MAX_DFU_CMD_QUEUE_SIZE);
    //wmalloc(DFU_DATA_QUEUE_MAX_SIZE*sizeof(uint8_t), ALLOC_NORMAL);
    //	wmalloc_init(heap_base, DFU_DATA_QUEUE_MAX_SIZE);
#endif

    printf("Initializing DFU Layer\n");
    usb_ctrl_callbacks_t dfu_usb_ctrl_callbacks = { // FIXME Replace handler pointers
        .class_rqst_handler             = dfu_class_parse_request,
        .vendor_rqst_handler            = NULL,
        .set_configuration_rqst_handler = NULL,
        .set_interface_rqst_handler     = NULL,
        .functional_rqst_handler        = dfu_functional_desc_request_handler,
        .mft_string_rqst_handler        = NULL,
    };
    usb_ctrl_init(dfu_usb_ctrl_callbacks, dfu_device_desc, dfu_configuration_desc);
    usb_driver_init();
    dfu_init_context();
    return;
}
