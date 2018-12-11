#include "autoconf.h"
#include "api/types.h"
#include "api/syscall.h"
#include "api/print.h"
#include "api/dfu.h"
#include "dfu_priv.h"
#include "usb.h"
#include "dfu_desc.h"
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

volatile bool ready_for_data_receive = true;

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

static volatile dfu_functional_descriptor_t dfu_fct_desc = {
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
    .wTransferSize = 0, /*set at init */
    .bcdDFUVersion = 0x0101
};

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
    printf("state: %x => %x\n", dfu_ctx->state, new_state);
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
 * Storing data handler, mostly dependent on
 * user layer callback/
 *********************************************/

/*
 * The USB content as been read into local buffer and is waiting to be stored
 * into the flash. This function does this
 */
static void dfu_store_data(void)
{
#if USB_DFU_DEBUG
    printf("storing data...\n");
#endif
    if (dfu_get_state() != DFUDNBUSY && dfu_get_state() != DFUDNLOAD_SYNC) {
        printf("Error! storing data in %d mode !", dfu_get_state());
        dfu_ctx->data_out_current_block_nb += 1;
        dfu_ctx->block_in_progress = 0;
        dfu_ctx->poll_start = 0;
        dfu_set_poll_timeout(0);
        dfu_ctx->data_to_store = 0;
        dfu_error(ERRUNKNOWN);
        return;
    }
    if (dfu_ctx->cb_write) {
        dfu_ctx->cb_write(dfu_ctx->data_out_buffer, dfu_ctx->data_out_length);
    }
    // now set the write action as done
    dfu_ctx->data_out_current_block_nb += 1;
    /* store request sent, no more data to store by now */
    dfu_ctx->data_to_store = 0;
    return;
}

void dfu_store_finished(void)
{
    /*
    Should be updated by the main loop. If upper layer received async IPC
    saying that data has been stored, then update these fields:
    */
    dfu_ctx->block_in_progress = 0;
    dfu_ctx->poll_start = 0;
    dfu_set_poll_timeout(0);
}

void dfu_load_finished(void)
{
    // FIXME: this part has to be implemented
}

/*
 * DNBUSY timeout is not timer-based. At each automaton schedule, we check
 * if:
 * 1) we are in DNBUSY state
 * 2) we spent more time than the configured timeout
 * if this is the case, we go back in DNLOAD_BUSY state
 */
static void dfu_handle_dnbusy_timeout(void)
{

    if (dfu_get_state() == DFUDNBUSY) {
        uint64_t ms;
        uint8_t ret;
        ret = sys_get_systick(&ms, PREC_MILLI);
        if (ret != SYS_E_DONE) {
            printf("Error: unable to get systick value !\n");
            goto err;
        }
        /* detecting timeout */
        if ((ms - dfu_ctx->poll_start) > dfu_ctx->poll_timeout_ms) {
            dfu_set_state(DFUDNLOAD_SYNC);
        }
    }
err:
    return;
}


/**********************************************
 * Handlers for each request
 *********************************************/

/*
 * Handle DFU_DETACH event
 */
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
    /* no action */
    return;

invalid_transition:
    dfu_error(ERRUNKNOWN);
    return;

}


/*
 * Handle DFU_DNLOAD event
 */
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
                if (setup_packet->wLength > dfu_ctx->transfert_size) {
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
                    ready_for_data_receive = false;
                    memset(dfu_ctx->data_out_buffer, 0, dfu_ctx->transfert_size);
                    usb_driver_setup_read(dfu_ctx->data_out_buffer, dfu_ctx->block_size,0);
                }
                /* This is a new download session (i.e. new file) */
                //dfu_set_state(next_state);
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
                } else if (setup_packet->wLength > dfu_ctx->transfert_size) {
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
                    ready_for_data_receive = false;
                    memset(dfu_ctx->data_out_buffer, 0, dfu_ctx->transfert_size);
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
    printf("dfu error ! input size too big! %x > %x\n",
            setup_packet->wLength, dfu_ctx->transfert_size);
    dfu_error(ERRSTALLEDPKT);
    return;
}


/*
 * Handle DFU_UPLOAD event
 */
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
                    if (setup_packet->wLength > dfu_ctx->transfert_size) {
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
    printf("dfu error ! input size too big! %x > %x\n",
            setup_packet->wLength, dfu_ctx->transfert_size);
    dfu_error(ERRSTALLEDPKT);
    return;

}

/*
 * Handle DFU_GETSTATUS event
 */
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
                if (dfu_ctx->block_in_progress == 1 || !ready_for_data_receive) {
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

                /* if a previous DNLOAD is not yet finished, wait before
                 * reconfiguring the USB device 
                 */
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

/*
 * Handle DFU_CLEAR_STATUS event
 */
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


/*
 * Handle DFU_GETSTATE event
 */
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

/*
 * Handle DFU_ABORT event
 */
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
 * End of request logics functions. Now let's prepare
 * ISR vs main thread communication mechanisms
 ******************************************************/

/*
 * ISR and main thread communicate using a queuing mechanism.
 * The ISR is enqueuing events, the main thread is dequeuing and
 * executing them.
 * Queue access is protected by the sys_lock() kernel mutual
 * exclusion mechanism dedicated to specific ISR-specific
 * problematic (see sys_lock() man page).
 * The DFU behave like the following:
 *
 * ISR                Main thread
 *  - (enqueue)          .
 *  |  ---> [1]          .
 *  -                    .
 *  - (enqueue)          .
 *  |  ---> [2]-[1]      .
 *  -                    -
 *  .               ---> | (dequeue & exec)
 *  .
 */

/*
 * request node, to be enqueue in handler mode, dequeue in
 * main thread
 */
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




/******************************************************
 * Global root handler dispatcher (handler mode)
 *
 * This function respond to the various DFU interrupts,
 * in ISR mode. This function only enqueue the various
 * request in order to let the main thread execute these
 * requests and handle the DFU automaton. This ISR function
 * is keeped simple and without any external I/O
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
    /**/

#if USB_DFU_DEBUG
    aprintf("[handler mode] ENQUEUINQ => state %d, req %d\n", dfu_get_state(), setup_packet->bRequest);
#endif
    ret = wmalloc((void**)&cur_req, sizeof(request_queue_node_t), ALLOC_NORMAL);
    if(ret){
        aprintf("Error while allocating queue !!!\n");
        dfu_error(ERRUNKNOWN);
        return;
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
 * Effective DFU state automaton dispatcher
 *****************************************************/

/*
 * Utility function use by the DFU automaton to release DFU
 * commands which have been dequeued and executed.
 */
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
 * Global root request executor (main thread)
 * This is the effective DFU automaton main function
 *
 * This function dequeue all the events queued in handler
 * mode, respecting the events order.
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
 * Data out handler, called by the USB stack when the requested data
 * configured during the dfu_request_dnload() in the USB stack has been
 * received in the USB device FIFO and copied in the task's buffer.
 */
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
    dfu_ctx->data_to_store = true;
    ready_for_data_receive = true;
}

/*
 * Data in handler, called by the USB stack when the task's fifo has been
 * fully read by the USB device in its own FIFO and sent to the host.
 */
static void dfu_data_in_handler(void)
{
    aprintf("end of USB read\n");
    dfu_ctx->data_to_store = true;
    ready_for_data_receive = true;
}


/****************************************************
 * DFU automaton main call
 **************************************************/

void dfu_exec_automaton(void)
{
    /* handle end of DNBUSY state */
    dfu_handle_dnbusy_timeout();
#if USB_DFU_DEBUG
    aprintf_flush();
#endif
    if (dfu_ctx->data_to_store) {
        /* request data store. Effective data store is not synchronous and
         * has to be acknowledge using dfu_store_finished() on the upper layer.
         * This permit to support DFU requests from host in the meantime.
         */
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


/****************************************************
 * Init functions
 **************************************************/

void dfu_init_context(void)
{
    uint16_t transfert_size = dfu_context.transfert_size ? dfu_context.transfert_size : 0;
    uint8_t  **buffer = dfu_context.data_out_buffer ? dfu_context.data_out_buffer : 0;
    dfu_write_block_cb_t write_cb = dfu_context.cb_write ? dfu_context.cb_write : 0;
    dfu_read_block_cb_t read_cb = dfu_context.cb_read ? dfu_context.cb_read : 0;

    dfu_context.block_in_progress = 0;
    dfu_context.session_in_progress = 0;
    dfu_context.status = OK;
    dfu_context.state = DFUIDLE;
    dfu_context.data_out_buffer = (uint8_t**)buffer;
    dfu_context.data_out_current_block_nb = 0;
    dfu_context.data_out_nb_blocks = 0;
    dfu_context.data_out_length = 0;
    dfu_context.data_in_buffer = (uint8_t**)buffer;
    dfu_context.data_in_nb_blocks = 0;
    dfu_context.data_in_current_block_nb = 0;
    dfu_context.data_in_length = 0;
    dfu_context.flash_address = 0x80000000;
    dfu_context.detach_timeout_ms = MAX_TIME_DETACH;
    dfu_context.detach_timeout_start = 0;
    dfu_context.poll_timeout_ms = MAX_POLL_TIMEOUT;
    dfu_context.poll_start = 0;
    dfu_context.block_size = transfert_size; /* TODO: this size must be a power of 2 and beetween 64 and 65k */
    dfu_context.transfert_size = transfert_size; /* TODO: this size must be a power of 2 and beetween 64 and 65k */
    dfu_context.firmware_size = 0;
    dfu_context.current_block_offset = 0;
    dfu_context.cb_read = read_cb;
    dfu_context.cb_write = write_cb;
    dfu_context.data_to_store = false;
}


void dfu_early_init(void)
{
    usb_driver_early_init(dfu_data_out_handler, dfu_data_in_handler);
}


void dfu_init(dfu_write_block_cb_t write_cb,
              dfu_read_block_cb_t  read_cb,
              uint8_t **buffer,
              uint16_t max_size)
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
    dfu_configuration_desc.functional_desc.wTransferSize = max_size;
    usb_ctrl_init(dfu_usb_ctrl_callbacks, dfu_device_desc, dfu_configuration_desc);
    /*
     * registering callbacks for read and write events actions
     * These callbacks are used to execute upper-layer handlers when a read
     * (upload) or a a write (download) action is requested, to execute
     * project specific events such as IPC, mass-storage write, etc.)
     */
    printf("initializing buffer to %x, size %x\n", buffer, max_size);
    dfu_context.cb_write = write_cb;
    dfu_context.cb_read = read_cb;
    dfu_fct_desc.wTransferSize = max_size;

/* if max_size is less than 64 or not a power of 2, it is an error */
    if (     (max_size < 64)
        || ! ((max_size && !(max_size & (max_size - 1)))))
    {
        printf("max_size %x is invalid\n", max_size);
    }

    dfu_init_context();
    dfu_context.data_out_buffer = buffer;
    dfu_context.data_in_buffer = buffer;
    dfu_context.block_size = 0;
    dfu_context.transfert_size = max_size;
    dfu_context.cb_read  = read_cb;
    dfu_context.cb_write = write_cb;
    usb_driver_init();
    return;
}
