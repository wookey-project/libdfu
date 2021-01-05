/*
 *
 * Copyright 2018 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
#include "autoconf.h"
#include "libc/types.h"
#include "libc/syscall.h"
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "libc/string.h"
#include "libc/queue.h"
#include "api/dfu.h"
#include "dfu_priv.h"
#include "dfu_desc.h"
#include "libc/sanhandlers.h"
#include "dfu_context.h"
#include "libusbctrl.h"

#define USB_DFU_DEBUG 0



/* This variable are read/write in separated temporal windows, making
 * volatile or critical section usage usless
 */
static uint8_t read_firmware_data_cmd = 0;

/********* USB layer handling ***************/
/*
 * These locks permit to detect if the below USB stack is ready or hasn't finished
 * yet data transmission/reception. These flags are updated by callbacks executed by
 * the USB below stack.
 * As the USB stack can't hold data while its previous job is not finished, we manage
 * the serialisation here
 */
static volatile bool dfu_usb_read_in_progress = false;
static volatile bool dfu_usb_write_in_progress = false;

static void dfu_usb_driver_setup_read_status(void)
{
	while((dfu_usb_read_in_progress == true) || (dfu_usb_write_in_progress == true)){
		continue;
	}
    // XXX: PTH: not for status read (i.e. clear NAK only)
	//dfu_usb_read_in_progress = true;
#if USB_DFU_DEBUG
	printf("==> READ dfu_usb_driver_setup_read_status\n");
#endif
    usb_backend_drv_ack(EP0, USB_BACKEND_DRV_EP_DIR_OUT);
	return;
}

static volatile uint32_t read_cnt = 0;
void dfu_usb_driver_setup_read(void *dst, uint32_t size){
	while((dfu_usb_read_in_progress == true) || (dfu_usb_write_in_progress == true)){
		continue;
	}
	dfu_usb_read_in_progress = true;
#if USB_DFU_DEBUG
	printf("==> READ %d dfu_usb_driver_setup_read %d\n", read_cnt, size);
#endif
	read_cnt++;
    /* XXX: replace '0' with ep->ep_id */
    usb_backend_drv_set_recv_fifo(dst, size, 0);
    usb_backend_drv_activate_endpoint(0, USB_BACKEND_DRV_EP_DIR_OUT);
	return;
}


static void dfu_usb_driver_stall_out(){
	while((dfu_usb_read_in_progress == true) || (dfu_usb_write_in_progress == true)){
		continue;
	}
	dfu_usb_write_in_progress = true;
#if USB_DFU_DEBUG
	printf("==> SEND dfu_usb_driver_stall_out\n");
#endif
    /* XXX: replace 0 with ep->ep_id */
    usb_backend_drv_stall(0, USB_BACKEND_DRV_EP_DIR_OUT);
	dfu_usb_write_in_progress = false;
	return;
}

static void dfu_usb_driver_setup_send_status(int status __attribute__((unused)))
{
	while((dfu_usb_read_in_progress == true) || (dfu_usb_write_in_progress == true)){
		continue;
	}
	dfu_usb_write_in_progress = true;
#if USB_DFU_DEBUG
	printf("==> SEND dfu_usb_driver_setup_send_status %d\n", status);
#endif
    /* XXX: change 0 with ep->ep_dir */
    usb_backend_drv_send_zlp(0);
    dfu_usb_write_in_progress = false;
	return;
}

void dfu_usb_driver_setup_send(const void *src, uint32_t size){
	while((dfu_usb_read_in_progress == true) || (dfu_usb_write_in_progress == true)){
		continue;
	}
	dfu_usb_write_in_progress = true;
#if USB_DFU_DEBUG
	printf("==> SEND dfu_usb_driver_setup_send %d\n", size);
#endif
    /* XXX: replace 0 with ep->ep_id */
    usb_backend_drv_send_data((uint8_t *)src, size, 0);
    usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
	return;
}

void dfu_usb_driver_setup_send_zlp(void){
    dfu_usb_driver_setup_send(0,0);
	dfu_usb_write_in_progress = false;
}




/********************************************/

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
static const char *unknown_request_name = "UKNOWN REQUEST";
static const char *print_request_name(dfu_request_t req){
	if(req <= 0x06){
		return request_name[req];
	}
	else{
		return unknown_request_name;
	}
}

static const char *state_name[] = {
    "APPIDLE",
    "APPDETACH",
    "DFUIDLE",
    "DFUDNLOAD_SYNC",
    "DFUDNBUSY",
    "DFUDNLOAD_IDLE",
    "DFUMANIFEST_SYNC",
    "DFUMANIFEST",
    "DFUMANIFEST_WAIT_RESET",
    "DFUUPLOAD_IDLE",
    "DFUERROR",
};
static const char *unknown_state_name = "UKNOWN STATE";
static const char *print_state_name(dfu_state_enum_t state){
	if(state <= 0x0A){
		return state_name[state];
	}
	else{
		return unknown_state_name;
	}
}
#endif



/*
 * Association between a request and a transition to a next state. This couple
 * depend on the current state and is use in the following structure
 */
typedef struct dfu_request_transition {
    uint8_t    request;
    uint8_t    target_state;
} dfu_request_transition_t;

volatile bool ready_for_data_receive = true;
volatile bool ready_for_data_send    = true;


/****************************************************************
 * DFU state automaton formal definition and associate utility
 * functions
 ***************************************************************/

/*
 * all allowed transitions and target states for each current state
 * empty fields are set as 0xff/0xff for request/state couple, which is
 * an inexistent state and request
 *
 * This table associate each state of the DFU automaton with up to
 * 5 potential allowed transitions/next_state couples. This permit to
 * easily detect:
 *    1) authorized transitions, based on the current state
 *    2) next state, based on the current state and current transition
 *
 * If the next_state for the current transision is keeped to 0xff, this
 * means that the current transition for the current state may lead to
 * multiple next state depending on other informations (see the official
 * DFU standard 1.1 state automaton (Figure A.1, p.28)). In this case,
 * the transition handler has to handle this manually.
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
                                 {USB_RQST_DFU_GET_STATUS,0xff},
                                 /* leave only on timeout, although:
                                  * timeout calculation is not accurate enough
                                  * tu avoid potential races with the host during
                                  * which a get_status() is performed just before
                                  * going back to DNLOAD_SYNC state.
                                  * For this particular case, we tolerate a short
                                  * temporal window at the end of the timeout in which
                                  * a get_status event can be received, if the timeout
                                  * is (ms-accurate) reached.
                                  */
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

/**********************************************
 * DFU getters and setters
 *********************************************/

uint32_t dfu_get_poll_timeout(void){
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
    return dfu_ctx->poll_timeout_ms;
}


static inline uint8_t dfu_get_state() {
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
    return dfu_ctx->state;
}

static inline uint8_t dfu_get_status() {
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
    return dfu_ctx->status;
}

uint8_t dfu_get_status_string_id() {
    // TODO
    return 0;
}

static inline void dfu_set_status(const dfu_status_enum_t new_status) {
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
    dfu_ctx->status = new_status;
}


static inline void dfu_set_state(const uint8_t new_state)
{
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
    if (new_state == 0xff) {
        printf("PANIC! this should never arrise !");
        while (1) {};
        return;
    }
#if USB_DFU_DEBUG
    printf("state: %x => %x\n", dfu_ctx->state, new_state);
#endif
    dfu_ctx->state = new_state;
}

void dfu_set_poll_timeout(uint32_t t, uint64_t timestamp)
{

    volatile dfu_context_t * dfu_ctx = dfu_get_context();
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
    dfu_ctx->poll_start = timestamp;
}

/******************************************************
 * DFU automaton management function (transition and
 * state check)
 *****************************************************/

/*!
 * \brief return the next automaton state
 *
 * The next state is returned depending on the current state
 * and the current request. In some case, it can be 0xff if multiple
 * next states are possible.
 *
 * \param current_state the current automaton state
 * \param request       the current transition request
 *
 * \return the next state, or 0xff
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

/*!
 * \brief Specify if the current request is valid for the current state
 *
 * See DFU standard 1.1 state automaton (Figure A.1, p.28)
 *
 * \param current_state the current automaton state
 * \param request       the current transition request
 *
 * \return true if the transition request is allowed for this state, or false
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
    printf("invalid transition from state %d, request %d\n", current_state, request);
    dfu_set_state(DFUERROR);
    return false;
}

/*********************************************************************
 * Mutexes, protection against race conditions...
 ********************************************************************/

/*
 * \brief entering a critical section
 *
 * During this critical section, any ISR is postponed to avoid any
 * race condition on variables shared in write-access between ISR and
 * main thread. See sys_lock() syscall API documentation.
 *
 * Critical sections must be as short as possible to avoid border
 * effects such as latency increase and ISR queue overloading.
 */
static inline void enter_critical_section(void)
{
    uint8_t ret;
    ret = sys_lock (LOCK_ENTER); /* Enter in critical section */
    if(ret != SYS_E_DONE){
        printf("Error: failed entering critical section!\n");
    }
    return;
}

/*
 * \brief leaving a critical section
 *
 * Reallow the execution of the previously postponed task ISR.
 */
static inline void leave_critical_section(void)
{
    uint8_t ret;
    ret = sys_lock (LOCK_EXIT);  /* Exit from critical section */
    if(ret != SYS_E_DONE){
        printf("Error: failed exiting critical section!\n");
    }
    return;
}

/**********************************************
 * DFU globals
 *********************************************/

typedef struct {
    uint16_t id;
    uint32_t size;
    uint8_t * data;
} dfu_data_block_t;


/**********************************************
 * DFU generic utility functions
 *********************************************/

/*!
 * Preparing the USB stack for stalling. This is requested
 * when a local 'block_in_progress' is still executed while
 * the host is requesting a status. The IP will then
 * automatically send stall events while we finished the
 * local treatement (read or write access)
 */
static void dfu_prepare_stall(void)
{
    dfu_usb_driver_stall_out();
}

/*
 * Manage various DFU errors. This can be:
 * - STALLEDPKT (get status while the block_in_progress is not finished)
 * - invalid transition request
 * - invalid input size (data too big for local buffer)
 * etc.
 * DFU errors are sent back to the host:
 * - for informational purpose
 * - to support resiliency (reseting upload/download work...)
 */
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



static void dfu_release_block(dfu_data_block_t *b)
{
    enter_critical_section();
    if(b != NULL){
        if(b->data != NULL){
#ifdef CONFIG_STD_MALLOC_LIGHT
            wfree((void**)&b->data);
#endif
        }

#ifdef CONFIG_STD_MALLOC_LIGHT
        wfree((void**)&b);
#endif
    }
    b = NULL;
    leave_critical_section();
}



static uint8_t dfu_validate_suffix(dfu_suffix_t * dfu_suffix __attribute__((unused)))
{
    // TODO
    return 1;
}


static uint8_t dfu_validate_sec_suffix(dfu_sec_metadata_hdr_t * dfu_sec_metadata_hdr __attribute__((unused)))
{
    // TODO
    return 1;
}


static uint8_t dfu_validate_memory_policy(uint32_t addr __attribute__((unused)),
        uint32_t length __attribute__((unused)))
{
    // TODO
    return 1;
}


/**********************************************
 * Storing and loading data handler, mostly dependent on
 * user layer callback/
 *********************************************/

/*
 * The USB content as been read into local buffer and is waiting to be stored
 * into the flash. This function does this
 */
static void dfu_store_data(void)
{
    volatile dfu_context_t * dfu_ctx = dfu_get_context();

    if (dfu_get_state() != DFUDNBUSY && dfu_get_state() != DFUDNLOAD_SYNC) {
        /* should not happend out of these two states. In that very case,
         * there is no block in progress as the automaton is not in download
         * mode
         */
        return;
    }
    dfu_backend_write(dfu_ctx->data_out_buffer, dfu_ctx->data_out_length, dfu_ctx->data_out_nb_blocks);
    // now set the write action as done
    dfu_ctx->data_out_current_block_nb += 1;
    /* store request sent, no more data to store by now */
    dfu_ctx->data_to_store = false;
    return;
}

static void dfu_load_data(void)
{
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
    /* INFO: size is given by setup packet but the block number is not
     * managed by the host, which only manage a file size */
    if (dfu_get_state() != DFUUPLOAD_IDLE) {
        /* should not happend out of these two states. In that very case,
         * there is no block in progress as the automaton is not in download
         * mode
         */
        return;
    }
    dfu_backend_read((uint8_t*)dfu_ctx->data_in_buffer, dfu_ctx->data_in_length);
    // now set the write action as done
    dfu_ctx->data_in_current_block_nb += 1;
    /* store request sent, no more data to store by now */
    return;
}


/*
 * This procedure is a *callback*. The DFU stack has no knowledge of
 * when the effective storage backend write is finished and request the
 * upper layer (the DFU application) to inform it when the write is finished.
 *
 * This function set the write action as finished and allows the host to
 * send the next chunk and permit (if the poll_timeout is 0) to fo back to DNLOAD_SYNC
 * or to DNLOAD_IDLE (depending on the current state)
 */
void dfu_store_finished(void)
{
#if USB_DFU_DEBUG
    printf("%s\n", __func__);
#endif
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
    /*
    Should be updated by the main loop. If upper layer received async IPC
    saying that data has been stored, then update these fields:
    */
    dfu_ctx->block_in_progress = 0;
    dfu_ctx->poll_start = 0;
    dfu_set_poll_timeout(0, 0);
}

/*
 * same principle as for the dfu_store_finished. This permit to inform
 * the DFU stack that its buffer has been fullfill with the firware chunk content and
 * can now be sent to the host.
 */
void dfu_load_finished(uint16_t bytes_read)
{
    volatile dfu_context_t * dfu_ctx = dfu_get_context();

    /* Here we should send the data stored in the buffer by the app into
     * the USB IP (upload mode) and then set block_in_progress as false
     * INFO:
     * The data sent is the number of effective read data, not the requested bytes
     * number. This is due to the end of upload mechanism which is based on the
     * detection on the received wLength value (from the host). When wLength is
     * smaller than the one requested, the host considering that the upload is
     * finished. bytes_read here is given by the DFU handling application depending
     * on the number of bytes read for this chunk by the storage backend.
     */
    /*
     * XXX: FIXME: no fragmentation here ! done by libusbctrl !!!
     */
    dfu_usb_driver_setup_send(dfu_ctx->data_in_buffer, bytes_read);
    if (bytes_read < dfu_ctx->data_in_length) {
        if ((bytes_read % 64) == 0) {
            /* Inform the host through sending a zlp packet that upload is finished */
            dfu_usb_driver_setup_send_zlp();
        }
        /* End of data read, going back to dfu_idle */
        dfu_ctx->data_in_nb_blocks = 0;
        dfu_ctx->data_in_length = 0;
        dfu_ctx->data_in_current_block_nb = 0;
        dfu_ctx->block_in_progress = 0;
        dfu_ctx->session_in_progress = 0;
        dfu_set_state(DFUIDLE);
    }
}


/**********************************************
 * Timeout management for DNBUSY state
 *********************************************/

/*
 * DNBUSY timeout is not timer-based. At each automaton schedule, we check
 * if:
 * 1) we are in DNBUSY state
 * 2) we spent more time than the configured timeout
 * if this is the case, we go back in DNLOAD_BUSY state
 */
static void dfu_handle_dnbusy_timeout(void)
{
    volatile dfu_context_t * dfu_ctx = dfu_get_context();

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
mbed_error_t dfu_request_detach(usbctrl_setup_pkt_t *setup_packet)
{
    /* Sanity check */
    if(setup_packet == NULL){
        goto invalid_transition;
    }
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
    return MBED_ERROR_NONE;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_INVSTATE;

}


/*
 * Handle DFU_DNLOAD event
 */
mbed_error_t dfu_request_dnload(usbctrl_setup_pkt_t *setup_packet)
{
#if USB_DFU_DEBUG
    printf("%s\n", __func__);
#endif
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
    /* Sanity check */
    if(setup_packet == NULL){
        printf("invalid setup pkt NULL\n");
        goto invalid_transition;
    }
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
                if (   dfu_ctx->can_download != true
                    || setup_packet->wLength                  == 0)
                {
                    goto download_not_supported;
                }
                if (setup_packet->wLength > dfu_ctx->transfert_size) {
                    goto size_too_big;
                } else {
                    /* dfu_ctx->data_out_current_block_nb;
                     * FIXME: this should be set to something */
                    dfu_ctx->data_out_nb_blocks = setup_packet->wValue;
                    dfu_ctx->data_out_length = setup_packet->wLength;
                    dfu_set_state(DFUDNLOAD_SYNC); /* We have data to dl */
                    dfu_ctx->block_in_progress = 1;
                    dfu_usb_driver_setup_send_status(0);
                    dfu_ctx->block_size = setup_packet->wLength;
                    dfu_ctx->session_in_progress = 1;
#if USB_DFU_DEBUG
                    printf("read %dB\n", dfu_ctx->block_size);
#endif
                    ready_for_data_receive = false;
#if USB_DFU_DEBUG
                    memset(dfu_ctx->data_out_buffer, 0, dfu_ctx->transfert_size);
#endif
                    dfu_usb_driver_setup_read(dfu_ctx->data_out_buffer, dfu_ctx->block_size);
                }
                /* This is a new download session (i.e. new file) */
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
                    dfu_set_state(DFUMANIFEST_SYNC);
                    dfu_usb_driver_setup_send_status(0);
                } else if (setup_packet->wLength > dfu_ctx->transfert_size) {
                    goto size_too_big;
                } else {
                    /* dfu_ctx->data_out_current_block_nb;
                     * FIXME: this should be set to something */
                    dfu_ctx->data_out_nb_blocks = setup_packet->wValue;
                    dfu_ctx->data_out_length = setup_packet->wLength;
                    dfu_set_state(DFUDNLOAD_SYNC); /* We have data to dl */
                    dfu_ctx->block_in_progress = 1;
                    dfu_usb_driver_setup_send_status(0);
                    dfu_ctx->block_size = setup_packet->wLength;
                    ready_for_data_receive = false;
#if USB_DFU_DEBUG
                    printf("read %dB\n", dfu_ctx->block_size);
                    memset(dfu_ctx->data_out_buffer, 0, dfu_ctx->transfert_size);
#endif
                    dfu_usb_driver_setup_read(dfu_ctx->data_out_buffer, dfu_ctx->block_size);
                }
                break;
            }
        default:
            printf("maybe a missing state: check automaton\n");
            break;
    }

    return MBED_ERROR_NONE;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_INVSTATE;

    /* FIXME proper error ?*/
download_not_supported:
    printf("dfu error: idle and can't download !\n");
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_UNSUPORTED_CMD;

size_too_big:
    printf("dfu error ! input size too big! %x > %x\n",
            setup_packet->wLength, dfu_ctx->transfert_size);
    dfu_error(ERRSTALLEDPKT);
    return MBED_ERROR_TOOBIG;
}


void dfu_leave_session_with_error(const dfu_status_enum_t new_status)
{
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
    enter_critical_section();
    dfu_set_state(DFUERROR);
    if (dfu_ctx->block_in_progress) {
        dfu_store_finished();
    }
    dfu_error(new_status);
    leave_critical_section();
}

/*
 * Handle DFU_UPLOAD event
 */
mbed_error_t dfu_request_upload(usbctrl_setup_pkt_t *setup_packet)
{
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
    /* Sanity check */
    if(setup_packet == NULL){
        goto invalid_transition;
    }
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
                    dfu_usb_driver_setup_send_status(0);
                } else {
                    /* just stay in current state, managing upload */
                    if (setup_packet->wLength > dfu_ctx->transfert_size) {
                        goto size_too_big;
                    } else {
                        dfu_ctx->data_in_nb_blocks = setup_packet->wValue;
                        dfu_ctx->data_in_length = setup_packet->wLength;
                        dfu_ctx->data_in_current_block_nb++;
                        dfu_ctx->block_in_progress = 1;
                        dfu_ctx->session_in_progress = 1;
                        dfu_ctx->block_size = setup_packet->wLength;
                        read_firmware_data_cmd = 1;
                        ready_for_data_send = false;
#if USB_DFU_DEBUG
                        printf("write %dB @%x\n", dfu_ctx->block_size, dfu_ctx->data_in_nb_blocks);
#endif
                        dfu_load_data();
                    }
                }
                break;
            }
        case DFUIDLE:
            {
                if (dfu_ctx->can_upload != true)
                {
                    goto upload_not_supported;
                } else {
                    /* just stay in current state, managing upload */
                    if (setup_packet->wLength > dfu_ctx->transfert_size) {
                        goto size_too_big;
                    } else {
                        dfu_ctx->data_in_nb_blocks = setup_packet->wValue;
                        dfu_ctx->data_in_length = setup_packet->wLength;
                        dfu_ctx->block_in_progress = 1;
                        dfu_ctx->session_in_progress = 1;
                        dfu_ctx->block_size = setup_packet->wLength;
                        ready_for_data_send = false;
                        dfu_set_state(next_state);
                        /* FIXME block number & size are needed */
#if USB_DFU_DEBUG
                        printf("write %dB @%x\n", dfu_ctx->block_size, dfu_ctx->data_in_nb_blocks);
#endif
                        dfu_load_data();
                    }
                }
                break;
            }
        default:
            printf("maybe a missing state: check automaton\n");
            break;
    }

    return MBED_ERROR_NONE;

invalid_transition:
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_INVSTATE;

    /* FIXME proper error ?*/
upload_not_supported:
    printf("dfu error ! idle mode and can't upload\n");
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_UNSUPORTED_CMD;

size_too_big:
    printf("dfu error ! input size too big! %x > %x\n",
            setup_packet->wLength, dfu_ctx->transfert_size);
    dfu_error(ERRSTALLEDPKT);
    return MBED_ERROR_TOOBIG;
}

/*
 * Handle DFU_GETSTATUS event
 */
mbed_error_t dfu_request_getstatus(usbctrl_setup_pkt_t *setup_packet, uint64_t timestamp)
{
#if USB_DFU_DEBUG
    printf("%s\n", __func__);
#endif
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
    /* Sanity check */
    if(setup_packet == NULL){
        goto invalid_transition;
    }
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

                dfu_usb_driver_setup_send((void*)&status, sizeof(status));
                dfu_usb_driver_setup_read_status();
                break;
            }
        case APPDETACH:
            {
                /* staying in APPDETACH */
                status.bStatus = dfu_get_status();
                status.bState = dfu_get_state();
                status.iString = dfu_get_status_string_id();

                dfu_usb_driver_setup_send((void*)&status, sizeof(status));
                dfu_usb_driver_setup_read_status();
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

                dfu_usb_driver_setup_send((void*)&status, sizeof(status));
                dfu_usb_driver_setup_read_status();
                break;
            }
        case DFUDNLOAD_SYNC:
            {
                if (dfu_ctx->block_in_progress == 1) {
                    /* Block transfert still in progress */
                    dfu_set_poll_timeout(MAX_POLL_TIMEOUT, timestamp);
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
                dfu_usb_driver_setup_send((void*)&status, sizeof(status));
                dfu_usb_driver_setup_read_status();
                break;
            }
        case DFUDNBUSY:
            {
                uint16_t tolerent_time = 4;
                /* we are tolerant as we consider that:
                 * the current ms calculation is equal to the moment when
                 * the ISR associated to the get_status event. In reality,
                 * both timestmap and poll_start are calculated a little
                 * later after the IRQ (they are calculated in the ISR context
                 * wish is postponed). As a consequence, if the timestamp
                 * calulcation is less late than the poll_start calculation,
                 * the difference may be shorter than the IRQ period.
                 * To avoid this, we include a tolerent time (in ms) to the
                 * calculation. This permit to support ISR execution gigue on
                 * highly loaded microcontrolers.
                 */
                if ((timestamp - dfu_ctx->poll_start + tolerent_time) < dfu_ctx->poll_timeout_ms) {
                    /* clearly, get_status arise *before* end of timeout !
                     * this is a violation of the DFU automaton */
                    uint32_t ts_low = (uint32_t)timestamp;
                    uint32_t ts_high = (uint32_t)(timestamp >> 32);
                    uint32_t ps_low = (uint32_t)dfu_ctx->poll_start;
                    uint32_t ps_high = (uint32_t)(dfu_ctx->poll_start >> 32);
                    uint32_t pt = (uint32_t)dfu_ctx->poll_timeout_ms;
                    printf("error: ts: %x%x ; ps: %x%x pt: %x\n", ts_high, ts_low, ps_high, ps_low, pt);
                    goto invalid_transition;
                }
                if (dfu_ctx->block_in_progress == 1) {
                    /* Block transfert still in progress, in that case,
                     * we reload the timeout and stay in DFNBUSY */
                    dfu_set_poll_timeout(MAX_POLL_TIMEOUT, timestamp);
                } else {
                    dfu_set_poll_timeout(0, 0);
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
                dfu_usb_driver_setup_send((void*)&status, sizeof(status));
                dfu_usb_driver_setup_read_status();
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

                dfu_usb_driver_setup_send((void*)&status, sizeof(status));
                dfu_usb_driver_setup_read_status();
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

                dfu_usb_driver_setup_send((void*)&status, sizeof(status));
                dfu_usb_driver_setup_read_status();
                /* inform the upper layer that the download is complete */
                dfu_backend_eof();
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

                dfu_usb_driver_setup_send((void*)&status, sizeof(status));
                dfu_usb_driver_setup_read_status();
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

                dfu_usb_driver_setup_send((void*)&status, sizeof(status));
                dfu_usb_driver_setup_read_status();
                break;
            }
        default:
            printf("maybe a missing state: check automaton\n");
            break;
    }
    return MBED_ERROR_NONE;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_INVSTATE;
}



/*
 * Handle DFU_CLEAR_STATUS event
 */
mbed_error_t dfu_request_clrstatus(usbctrl_setup_pkt_t *setup_packet)
{
    volatile dfu_context_t *dfu_ctx = dfu_get_context();
    /* Sanity check */
    if(setup_packet == NULL){
        goto invalid_transition;
    }
    /* Sanity check and next state detection */
    uint8_t next_state;
    device_dfu_status_t status;
    memset((void*)&status, 0, sizeof(device_dfu_status_t));
    if (!dfu_is_valid_transition(dfu_get_state(), setup_packet->bRequest)) {
        goto invalid_transition;
    }
    next_state = dfu_next_state(dfu_get_state(), setup_packet->bRequest);

    /* effective transition execution (if needed) */
    dfu_init_context(dfu_ctx);
    dfu_set_state(next_state);
    dfu_usb_driver_setup_send_status(0);
    return MBED_ERROR_NONE;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_INVSTATE;
}


/*
 * Handle DFU_GETSTATE event
 */
mbed_error_t dfu_request_getstate(usbctrl_setup_pkt_t *setup_packet)
{
    /* Sanity check */
    if(setup_packet == NULL){
        goto invalid_transition;
    }
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

                dfu_usb_driver_setup_send((void*)&state, 1);
                dfu_usb_driver_setup_read_status();
                break;
            }
        default:
            printf("maybe a missing state: check automaton\n");
            break;
    }
    return MBED_ERROR_NONE;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_INVSTATE;
}

/*
 * Handle DFU_ABORT event
 */
int dfu_request_abort(usbctrl_setup_pkt_t *setup_packet)
{
    volatile dfu_context_t *dfu_ctx = dfu_get_context();
    /* Sanity check */
    if(setup_packet == NULL){
        goto invalid_transition;
    }
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
                dfu_init_context(dfu_ctx);
                dfu_set_state(next_state);
                dfu_usb_driver_setup_send_status(0);
                break;
            }
        default:
            printf("maybe a missing state: check automaton\n");
            break;

    }
    return MBED_ERROR_NONE;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_INVSTATE;
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
typedef struct __attribute__((packed)) {
    uint64_t                 timestamp;
    dfu_request_t            request;
    usbctrl_setup_pkt_t  setup_packet;
} request_queue_node_t;

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
static mbed_error_t dfu_class_parse_request(uint32_t usbdci_handler __attribute__((unused)),
                                            usbctrl_setup_pkt_t *setup_packet)
{
    uint8_t ret;
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint64_t ms;

    /* Sanity check */
    if(setup_packet == NULL){
        printf("NULL packet\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    ret = sys_get_systick(&ms, PREC_MILLI);
    if (ret != SYS_E_DONE) {
        printf("timestamping error\n");
        errcode = MBED_ERROR_INVCREDENCIALS;
        goto err;
    }
    request_queue_node_t *cur_req = NULL;

    /* We have received a setup packet: we can release the USB read lock
     * There is no possible race condition on this variable as temporal
     * windows on which this variable is set in mainthread and ISR are
     * separated. As a consequence, lock or critical sections is not required
     * for accessing this variable
     */
    dfu_usb_read_in_progress = false;

    /*
     * Request unknown (not DFU standard)
     */
    if (setup_packet->bRequest > USB_RQST_DFU_ABORT) {
#if USB_DFU_DEBUG
        printf("dfu: %s: unknown request\n", __func__);
#endif
        errcode = MBED_ERROR_UNSUPORTED_CMD;
        goto err;
    }

    /*
     * Here we prepare the cell before enqueuing it, The DFU request is queued
     * in order to be executed in main thread mode. The ISR only handle
     * requests enquing
     */
#if USB_DFU_DEBUG
    printf("[handler mode] ENQUEUINQ => state %s, req %s\n", print_state_name(dfu_get_state()), print_request_name(setup_packet->bRequest));
#endif
    ret = wmalloc((void**)&cur_req, sizeof(request_queue_node_t), ALLOC_NORMAL);
    if(ret) {
        printf("Error while allocating queue !!!\n");
        errcode = MBED_ERROR_NOMEM;
        dfu_error(ERRUNKNOWN);
        goto err;
    }

#if USB_DFU_DEBUG
    printf("req: %s\n", print_request_name(setup_packet->bRequest));
#endif
    cur_req->request = setup_packet->bRequest;
    cur_req->timestamp = ms;
    memcpy((void*)&cur_req->setup_packet, setup_packet, sizeof(usbctrl_setup_pkt_t));
    /*
     * Enqueue and set queue as not empty
     */
    errcode = queue_enqueue(dfu_cmd_queue, cur_req);
    if (errcode == MBED_ERROR_BUSY) {
        printf("[ISR] Error! queue is busy!\n");
    }
if (errcode == MBED_ERROR_NOMEM) {
        printf("[ISR] Error! queue is full!\n");
    }
    dfu_cmd_queue_empty = 0;

err:
    return errcode;
}

/******************************************************
 * Effective DFU state automaton dispatcher
 *****************************************************/

/*
 * Utility function use by the DFU automaton to release DFU
 * commands which have been dequeued and executed.
 */
static void dfu_release_current_dfu_cmd(request_queue_node_t **current_dfu_cmd)
{
    if(current_dfu_cmd == NULL){
        return;
    }
    if (*current_dfu_cmd != NULL) {
        if (wfree((void**)current_dfu_cmd)) {
            printf("freeing current command failed\n");
            dfu_error(ERRUNKNOWN);
        }
    }
    *current_dfu_cmd = NULL;
    return;
}


/******************************************************
 * Global root request executor (main thread)
 * This is the effective DFU automaton main function
 *
 * This function dequeue all the events queued in handler
 * mode, respecting the events order.
 *****************************************************/
#if __GNUC__ > 8
/*
 * INFO: Here, we cast a packed struct address in a uint32_t pointer for memset().
 * This is *not* an error.
 * Gcc 9 warning is a false positive.
 */
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Waddress-of-packed-member"
#endif
static mbed_error_t dfu_class_execute_request(void)
{
    request_queue_node_t *current_dfu_cmd_p = NULL;
    request_queue_node_t current_dfu_cmd;
    mbed_error_t         ret = MBED_ERROR_NONE;
    if(dfu_cmd_queue_empty == 1)
    {
        return MBED_ERROR_NONE;
    }

    enter_critical_section();
    if (queue_dequeue(dfu_cmd_queue, (void**)&current_dfu_cmd_p) != MBED_ERROR_NONE) {
        printf("Unable to dequeue command!\n");
        leave_critical_section();
	return MBED_ERROR_NOSTORAGE;
    }
    current_dfu_cmd = *current_dfu_cmd_p;
    dfu_release_current_dfu_cmd(&current_dfu_cmd_p);
    if(queue_is_empty(dfu_cmd_queue)) {
        dfu_cmd_queue_empty = 1;
    }
    leave_critical_section();
#if USB_DFU_DEBUG
    printf("[main thread] DEQUEUING, state is: ");
    dfu_state_enum_t old_state, new_state;
    old_state = dfu_get_state();
#endif
    switch( current_dfu_cmd.setup_packet.bRequest ) {
	/* Note: (void*) cast to silence clang [-Werror,-Waddress-of-packed-member]
	 * Our architecture allows unaligned accesses, so this should be OK.
	 */
        case USB_RQST_DFU_DETACH:
#if USB_DFU_DEBUG
            printf("DFU_DETACH\n");
#endif
            if((ret = dfu_request_detach((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet)))) {
                goto err;
            }
            break;

        case USB_RQST_DFU_DNLOAD:
#if USB_DFU_DEBUG
            printf("DFU_DNLOAD\n");
#endif
            if((ret = dfu_request_dnload((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet)))) {
                goto err;
            }
            break;

        case USB_RQST_DFU_UPLOAD:
#if USB_DFU_DEBUG
            printf("DFU_UPLOAD\n");
#endif
            if((ret = dfu_request_upload((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet)))) {
                goto err;
            }
            break;

        case USB_RQST_DFU_GET_STATUS:
#if USB_DFU_DEBUG
            printf("DFU_GET_STATUS\n");
#endif
            if((ret = dfu_request_getstatus((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet), current_dfu_cmd.timestamp))) {
                goto err;
            }
            break;

        case USB_RQST_DFU_CLEAR_STATUS:
#if USB_DFU_DEBUG
            printf("DFU_CLEAR_STATUS\n");
#endif
            if((ret = dfu_request_clrstatus((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet)))) {
                goto err;
            }
            break;

        case USB_RQST_DFU_GET_STATE:
#if USB_DFU_DEBUG
            printf("DFU_GET_STATE\n");
#endif
            if((ret = dfu_request_getstate((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet)))) {
                goto err;
            }
            break;

        case USB_RQST_DFU_ABORT:
#if USB_DFU_DEBUG
            printf("DFU_GET_ABORT\n");
#endif
            if((ret = dfu_request_abort((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet)))) {
                goto err;
            }
            break;

        default:
            printf("dfu: %s: unknown request %d\n", __func__, current_dfu_cmd.setup_packet.bRequest);
            dfu_error(ERRUNKNOWN);
    }
#if USB_DFU_DEBUG
    new_state = dfu_get_state();
    printf("[XXX] WE HAVE TRANSITIONED FROM %s to %s, the request was %s\n", print_state_name(old_state), print_state_name(new_state), print_request_name(current_dfu_cmd.setup_packet.bRequest));
#endif

err:
    return ret;
}
#if __GNUC__ > 8
#pragma GCC diagnostic pop
#endif

/*
 * Data out handler, called by the USB stack when the requested data
 * configured during the dfu_request_dnload() in the USB stack has been
 * received in the USB device FIFO and copied in the task's buffer.
 */
static mbed_error_t dfu_data_out_handler(uint32_t dev_id __attribute__((unused)),
                                         uint32_t size __attribute__((unused)),
                                         uint8_t ep_id __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
#if USB_DFU_DEBUG
    printf("end of USB read\n");
#endif
    /* FIXME: size passed here should be checked in comparison with
     * the size passed in the previous request */

    /* all data received from host. This handler is executed by the lower
     * USB stack at the end of the effective usb_status_read() call.
     * Here, we set a flag to request the main thread to effetively copy the
     * buffer content into the flash. When this is done, the flag is
     * lowered and the block_in_pogress field of the dfu context is set to 0.
     */
     ready_for_data_receive = true;
     dfu_usb_read_in_progress = false;
     dfu_ctx->data_to_store = true;
     return errcode;
}

/*
 * Data in handler, called by the USB stack when the task's fifo has been
 * fully read by the USB device in its own FIFO and sent to the host.
 */
static mbed_error_t dfu_data_in_handler(uint32_t dev_id __attribute__((unused)),
                                        uint32_t size __attribute__((unused)),
                                        uint8_t ep_id __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
#if USB_DFU_DEBUG
    printf("[ISR] end of USB write\n");
#endif
    /* USB IP write access is now finished */
    dfu_usb_write_in_progress = false;

    if (dfu_get_state() == DFUUPLOAD_IDLE) {
        /* The write action on the USB output fifo is finished
         * In DFUUPLOAD mode, this means that the flash data has
         * been successfully pushed into the device and we can handle
         * the next chunk
         */
        dfu_ctx->block_in_progress = 0;
        dfu_ctx->poll_start = 0;
        dfu_set_poll_timeout(0, 0);
    }
     return errcode;
}


/****************************************************
 * DFU automaton main call
 **************************************************/

mbed_error_t dfu_exec_automaton(void)
{
    volatile dfu_context_t * dfu_ctx = dfu_get_context();
    /* handle end of DNBUSY state */
    dfu_handle_dnbusy_timeout();
    if (dfu_ctx->data_to_store == true) {
        /* request data store. Effective data store is not synchronous and
         * has to be acknowledge using dfu_store_finished() on the upper layer.
         * This permit to support DFU requests from host in the meantime.
         */
        dfu_store_data();
    }

    /* all DFU automaton execution */
    if(dfu_class_execute_request()){
        goto err;
    }
    return 0;

err:
    return -1;
}


/****************************************************
 * Init functions
 **************************************************/


mbed_error_t dfu_declare(uint32_t usbdci_handler)
{
    /* Register our callbacks */
    ADD_LOC_HANDLER(dfu_data_out_handler)
    ADD_LOC_HANDLER(dfu_data_in_handler)
    ADD_LOC_HANDLER(dfu_class_parse_request)
    ADD_LOC_HANDLER(dfu_get_descriptor)

    volatile dfu_context_t * dfu_ctx = dfu_get_context();
    /* initialize DFU level context content */
    dfu_init_context(dfu_ctx);

    /* initialize libusbctrl interface in DFU context */
    dfu_ctx->iface.usb_class = USB_CLASS_DFU;
    dfu_ctx->iface.usb_subclass = USB_SUBCLASS_DFU;
    dfu_ctx->iface.usb_protocol = USB_PROTOCOL_DFU_DFU;
    dfu_ctx->iface.dedicated = false;
    dfu_ctx->iface.rqst_handler = dfu_class_parse_request;
    dfu_ctx->iface.class_desc_handler = dfu_get_descriptor;
    dfu_ctx->iface.usb_ep_number = 2;

    dfu_ctx->iface.eps[0].type        = USB_EP_TYPE_CONTROL;
    dfu_ctx->iface.eps[0].dir         = USB_EP_DIR_OUT;
    dfu_ctx->iface.eps[0].attr        = USB_EP_ATTR_NO_SYNC;
    dfu_ctx->iface.eps[0].usage       = USB_EP_USAGE_DATA;
    dfu_ctx->iface.eps[0].pkt_maxsize = 64; /* mpsize on EP0 (standard on USB 1.1, 2.0) */
    dfu_ctx->iface.eps[0].ep_num      = 0; /* this may be updated by libctrl */
    dfu_ctx->iface.eps[0].handler     = dfu_data_out_handler;

    dfu_ctx->iface.eps[1].type        = USB_EP_TYPE_CONTROL;
    dfu_ctx->iface.eps[1].dir         = USB_EP_DIR_IN;
    dfu_ctx->iface.eps[1].attr        = USB_EP_ATTR_NO_SYNC;
    dfu_ctx->iface.eps[1].usage       = USB_EP_USAGE_DATA;
    dfu_ctx->iface.eps[1].pkt_maxsize = 64; /* mpsize on EP0 (standard on USB 1.1, 2.0) */
    dfu_ctx->iface.eps[1].ep_num      = 0; /* this may be updated by libctrl */
    dfu_ctx->iface.eps[1].handler     = dfu_data_in_handler;

    /* declare interface against libsubctrl */
    return usbctrl_declare_interface(usbdci_handler, (usbctrl_interface_t*)&dfu_ctx->iface);
}


mbed_error_t dfu_init(uint8_t **buffer,
                      uint16_t max_size)
{

    volatile dfu_context_t *dfu_ctx = dfu_get_context();
    mbed_error_t err;
#ifdef CONFIG_STD_MALLOC_LIGHT
    wmalloc_init();

    err = queue_create(MAX_DFU_CMD_QUEUE_SIZE, &dfu_cmd_queue);
    if (err != MBED_ERROR_NONE) {
        printf("Unable to create queue !\n");
        return err;
    }
#endif

    printf("Initializing DFU Layer\n");
    /*
     * registering callbacks for read and write events actions
     * These callbacks are used to execute upper-layer handlers when a read
     * (upload) or a a write (download) action is requested, to execute
     * project specific events such as IPC, mass-storage write, etc.)
     */

/* if max_size is less than 64 or not a power of 2, it is an error */
    if (     (max_size < 64)
        || ! ((max_size && !(max_size & (max_size - 1)))))
    {
        printf("max_size %x is invalid\n", max_size);
    }
    dfu_ctx->data_out_buffer = buffer;
    dfu_ctx->data_in_buffer = buffer;
    dfu_ctx->block_size = 0;
    dfu_ctx->transfert_size = max_size;
    return MBED_ERROR_NONE;
}

mbed_error_t dfu_reinit(void)
{
    volatile dfu_context_t *dfu_ctx = dfu_get_context();
    /* effective transition execution (if needed) */
    dfu_init_context(dfu_ctx);
    dfu_set_state(DFUIDLE);
    return MBED_ERROR_NONE;
}


