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
#include "libc/sync.h"
#include "libc/nostd.h"
#include "libc/string.h"
#include "libc/queue.h"
#include "api/dfu.h"
#include "dfu_priv.h"
#include "dfu_desc.h"
#include "libc/sanhandlers.h"
#include "dfu_context.h"
#include "libusbctrl.h"
#ifdef __FRAMAC__
#include "framac/entrypoint.h"
#endif


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
static bool dfu_usb_read_in_progress = false;
static bool dfu_usb_write_in_progress = false;

/* pmo moved at the beginning of file for frama-c */
bool ready_for_data_receive = true;
bool ready_for_data_send    = true;

/*@ assigns GHOST_opaque_drv_privates , dfu_usb_write_in_progress;
  @ ensures dfu_usb_write_in_progress == \false;  */
static inline void dfu_usb_driver_setup_send_zlp(void){
    usb_backend_drv_send_zlp(0);
	set_bool_with_membarrier(&dfu_usb_write_in_progress, false);
}

#if CONFIG_USR_LIB_DFU_DEBUG
static uint32_t read_cnt = 0;
#endif

/*@
  @ requires
        \separated(
          &GHOST_opaque_libusbdci_privates,
          &GHOST_num_ctx,
          &dfu_usb_read_in_progress, &dfu_usb_write_in_progress,
          &GHOST_opaque_drv_privates
          );
	  @ assigns ready_for_data_receive,GHOST_opaque_drv_privates,
	  dfu_usb_read_in_progress, dfu_context.data_to_store,
	  dfu_usb_write_in_progress, dfu_context.block_in_progress,
	  dfu_context.poll_start, dfu_context.poll_timeout_ms; 


      
*/
void dfu_usb_driver_setup_read(uint8_t *dst, uint32_t size){
#ifdef __FRAMAC__ //pmo to check
    /*@ loop assigns ready_for_data_receive, dfu_usb_read_in_progress,
    dfu_context.data_to_store; */
	while(dfu_usb_read_in_progress == true){
	  request_data_membarrier();
	  /* emulate asyncrhonous events */
	  dfu_data_out_handler(0,0,0);
	  continue;
	}
    /*@ loop assigns dfu_usb_write_in_progress, dfu_context.block_in_progress,
	  dfu_context.poll_start, dfu_context.poll_timeout_ms; */
	while(dfu_usb_write_in_progress == true){
	  request_data_membarrier();
	  /* emulate asyncrhonous events */
	  dfu_data_in_handler(0,0,0);
	  continue;
	}
#else
	while((dfu_usb_read_in_progress == true) || (dfu_usb_write_in_progress == true)){
	  request_data_membarrier();
	    continue;
	}
#endif
	set_bool_with_membarrier(&dfu_usb_read_in_progress, true);
#if CONFIG_USR_LIB_DFU_DEBUG
	log_printf("==> READ %d dfu_usb_driver_setup_read %d\n", read_cnt, size);
	set_u32_with_membarrier(&read_cnt, read_cnt + 1);
#endif
    /* XXX: replace '0' with ep->ep_id */
    usb_backend_drv_set_recv_fifo(dst, size, 0);
    usb_backend_drv_activate_endpoint(0, USB_BACKEND_DRV_EP_DIR_OUT);
	return;
}


/*@
  @ requires \separated(&GHOST_opaque_drv_privates, &dfu_usb_write_in_progress);
  @ assigns ready_for_data_receive,GHOST_opaque_drv_privates, dfu_usb_read_in_progress,
            dfu_context.data_to_store, dfu_usb_write_in_progress,
	    dfu_context.block_in_progress, dfu_context.poll_start, dfu_context.poll_timeout_ms;  */
static void dfu_usb_driver_stall_out(void){
#ifdef __FRAMAC__ //pmo to check
  /*@ loop assigns ready_for_data_receive, dfu_usb_read_in_progress,
    dfu_context.data_to_store; */
	while(dfu_usb_read_in_progress == true){
	  request_data_membarrier();
	  /* emulate asyncrhonous events */
	  dfu_data_out_handler(0,0,0);
	  continue;
	}
	/*@ loop assigns dfu_usb_write_in_progress, dfu_context.block_in_progress,
	  dfu_context.poll_start, dfu_context.poll_timeout_ms; */
	while(dfu_usb_write_in_progress == true){
	  request_data_membarrier();
	  /* emulate asyncrhonous events */
	  dfu_data_in_handler(0,0,0);
	  continue;
	}
#else
	while((dfu_usb_read_in_progress == true) || (dfu_usb_write_in_progress == true)){
	  request_data_membarrier();
	    continue;
	}
#endif
	set_bool_with_membarrier(&dfu_usb_write_in_progress, true);
	log_printf("==> SEND dfu_usb_driver_stall_out\n");
    /* XXX: replace 0 with ep->ep_id */
	usb_backend_drv_stall(0, USB_BACKEND_DRV_EP_DIR_OUT);
	set_bool_with_membarrier(&dfu_usb_write_in_progress, false);
	return;
}

/*@
  @ requires \separated(&dfu_usb_write_in_progress, &GHOST_opaque_drv_privates);
  @ assigns dfu_usb_write_in_progress, GHOST_opaque_drv_privates;
  */
static void dfu_usb_driver_setup_send_status(int status __attribute__((unused)))
{
    /* XXX: change 0 with ep->ep_dir */
    dfu_usb_driver_setup_send_zlp();
	return;
}

/*@
  @ requires \separated(&dfu_usb_write_in_progress, &GHOST_opaque_drv_privates);
  @ assigns ready_for_data_receive,GHOST_opaque_drv_privates,
            dfu_usb_read_in_progress,
            dfu_context.data_to_store, dfu_usb_write_in_progress,
	    dfu_context.block_in_progress, dfu_context.poll_start,
	    dfu_context.poll_timeout_ms, GHOST_in_eps[0].state;
 */
// PMO to check j'ai modifie le type d'arguement 1 de void * en uint8_t *
void dfu_usb_driver_setup_send(const uint8_t *src, uint32_t size) {
#ifdef __FRAMAC__ //pmo to check
  /*@ loop assigns ready_for_data_receive, dfu_usb_read_in_progress,
    dfu_context.data_to_store; */
	while(dfu_usb_read_in_progress == true){
	  request_data_membarrier();
	  /* emulate asyncrhonous events */
	  dfu_data_out_handler(0,0,0);
	  continue;
	}
	/*@ loop assigns dfu_usb_write_in_progress, dfu_context.block_in_progress,
	  dfu_context.poll_start, dfu_context.poll_timeout_ms; */
	while(dfu_usb_write_in_progress == true){
	  request_data_membarrier();
	  /* emulate asyncrhonous events */
	  dfu_data_in_handler(0,0,0);
	  continue;
	}
#else
	while((dfu_usb_read_in_progress == true) || (dfu_usb_write_in_progress == true)){
	  request_data_membarrier();
	    continue;
	}
#endif
	set_bool_with_membarrier(&dfu_usb_write_in_progress, true);
	log_printf("==> SEND dfu_usb_driver_setup_send %d\n", size);
	/* XXX: replace 0 with ep->ep_id */
	usb_backend_drv_send_data((uint8_t *)src, size, 0);
	usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
	return;
}





/********************************************/

#if CONFIG_USR_LIB_DFU_DEBUG
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

/*@
  @ assigns \nothing;
  @ ensures \result == dfu_context.poll_timeout_ms;
 */
#ifndef __FRAMAC__
static
#endif
uint32_t dfu_get_poll_timeout(void){
    dfu_context_t * dfu_ctx = dfu_get_context();
    return dfu_ctx->poll_timeout_ms;
}

/*@
  @ assigns \nothing;
  @ ensures \result == dfu_context.state;
 */
#ifndef __FRAMAC__
static inline
#endif
uint8_t dfu_get_state() {
    dfu_context_t * dfu_ctx = dfu_get_context();
    return dfu_ctx->state;
}

/*@
  @ assigns \nothing;
  @ ensures \result == dfu_context.status;
 */
#ifndef __FRAMAC__
static inline
#endif
uint8_t dfu_get_status() {
    dfu_context_t * dfu_ctx = dfu_get_context();
    return dfu_ctx->status;
}

/*@
  @ assigns \nothing;
 */
#ifndef __FRAMAC__
static
#endif
uint8_t dfu_get_status_string_id() {
    // TODO
    return 0;
}

/*@
  @ assigns dfu_context.status;
  @ ensures dfu_context.status == new_status;
 */
#ifndef __FRAMAC__
static inline
#endif
void dfu_set_status(const dfu_status_enum_t new_status) {
    dfu_context_t * dfu_ctx = dfu_get_context();
    dfu_ctx->status = new_status;
    request_data_membarrier();
}


/*@
  @ requires \valid(&dfu_context.state);
  @ requires is_valid_dfu_state(new_state);

  @ behavior pb :
  @ assumes new_state >= DFUERROR;
  @ assigns dfu_context.state;
  @ ensures dfu_context.state == DFUERROR;
  @
  @ behavior ok :
  @ assumes new_state < DFUERROR;
  @ assigns  dfu_context.state;
  @ ensures dfu_context.state == new_state;
  @
  @ complete behaviors;
  @ disjoint behaviors;
 */
#ifndef __FRAMAC__
static inline
#endif
void dfu_set_state(const uint8_t new_state)
{
    dfu_context_t * dfu_ctx = dfu_get_context();
    // CDE : new test to check invalid dfu state
    if (new_state >= DFUERROR) {
        /* should never happen ! fault protection code */
        log_printf("PANIC! this should never happen. goto DFUERROR !");
        dfu_ctx->state = DFUERROR;
        goto err;
    }
    log_printf("state: %x => %x\n", dfu_ctx->state, new_state);
    dfu_ctx->state = new_state;
err:
    request_data_membarrier();
    return;
}


/*@
  @ assigns dfu_context.poll_timeout_ms,dfu_context.poll_start;
  @ ensures dfu_context.poll_timeout_ms == t && dfu_context.poll_start == timestamp;
 */
#ifndef __FRAMAC__
static
#endif
void dfu_set_poll_timeout(uint16_t t, uint64_t timestamp)
{
    dfu_context_t * dfu_ctx = dfu_get_context();
    uint64_t ms;
    uint8_t ret;

    log_printf("setting poll_timeout_ms to %d\n", t);
    dfu_ctx->poll_timeout_ms = t;
    ret = sys_get_systick(&ms, PREC_MILLI);
    if (ret != SYS_E_DONE) {
        log_printf("Error: unable to get systick value !\n");
    }
    dfu_ctx->poll_start = timestamp;
    request_data_membarrier();
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


/* @
  @ requires APPIDLE <= current_state <= DFUERROR;
  @ requires USB_RQST_DFU_DETACH <= request <= USB_RQST_DFU_ABORT;
  @ assigns \nothing;
  // TODO: specify function contract
 */

/* CDE function identical as usbctrl_next_state so fcn contract is similar
   TODO : ensure \result == 0xff cannot be easily prooved, bacause transition table does not define precisely target_state
*/

/*@
  @ requires is_valid_dfu_state(current_state);
  @ requires is_valid_dfu_request(request);
  @ assigns \nothing ;
  @ ensures (\result != 0xff) ==> (\exists integer i; 0 <= i < 5 && dfu_automaton[current_state].req_trans[i].request == request
            && \result == dfu_automaton[current_state].req_trans[i].target_state) ;
  @ ensures (\result == 0xff) ==> (\forall integer i; 0 <= i < 5 ==> dfu_automaton[current_state].req_trans[i].request != request);
*/

static uint8_t dfu_next_state(dfu_state_enum_t  current_state, dfu_request_t    request)
{
  /*@
      @ loop invariant 0 <= i <= 5 ;
      @ loop invariant \valid_read(dfu_automaton[current_state].req_trans + (0..(5 -1)));
      @ loop invariant (\forall integer prei ; 0 <= prei < i ==> dfu_automaton[current_state].req_trans[prei].request != request) ;
      @ loop assigns i ;
      @ loop variant 5 -i ;
  */

  for (uint8_t i = 0; i < 5; ++i) {
        if (dfu_automaton[current_state].req_trans[i].request == request) {
            return (dfu_automaton[current_state].req_trans[i].target_state);
        }
    }
    /* fallback, no corresponding request found for  this state */
    /*@ assert (\forall integer i; 0 <= i < 5 ==> dfu_automaton[current_state].req_trans[i].request != request) ; */
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
/* @

  @ requires USB_RQST_DFU_DETACH <= request <= USB_RQST_DFU_ABORT;
  @ requires \separated(dfu_automaton + (0 .. DFUERROR),&dfu_context.state);*/

// PMO en mode behavior KO assigns ne passe pas
/* CDE j'ai eu le même probleme avec usbctrl_is_valid_transition, je n'ai pas mis de behavior du coup
       les behaviors compliquent les preuves pour les fonctions appelantes en plus  */

/* @
  @ requires APPIDLE <= current_state <= DFUERROR;
  @ requires \valid_read(dfu_automaton[current_state].req_trans + (0 .. 4));
  @ requires \separated(&GHOST_opaque_libusbdci_privates, &GHOST_num_ctx, (struct __anonstruct_dfu_automaton_83 const *)dfu_automaton + (..),
  &num_ctx, &dfu_usb_read_in_progress, &dfu_usb_write_in_progress,
  &ready_for_data_receive, &ready_for_data_send,  &dfu_context.state );
  @
  @ behavior OK:
  @ assumes  \exists integer i; 0 <= i < 5 && dfu_automaton[current_state].req_trans[i].request == request ;
  @ assigns \nothing;
  @ ensures \result == \true;
  @
  @ behavior KO:
  @ assumes (\forall integer i; 0 <= i < 5 ==> dfu_automaton[current_state].req_trans[i].request != request)  ;
  @ assigns dfu_context.state;
  @ ensures dfu_context.state == DFUERROR && \result == \false;
  @
  @ complete behaviors;
  @ disjoint behaviors;
 */

// CDE TODO : ensures proove equivalence for \result == \false

/*@
  @ requires is_valid_dfu_state(current_state);
  @ requires is_valid_dfu_request(request);
  @ requires is_valid_dfu_state(dfu_context.state);
  @ requires \valid_read(dfu_automaton[current_state].req_trans + (0 .. 4));
  @ requires \separated(&GHOST_opaque_libusbdci_privates, &GHOST_num_ctx, (struct __anonstruct_dfu_automaton_83 const *)dfu_automaton + (..),
  &num_ctx, &dfu_usb_read_in_progress, &dfu_usb_write_in_progress,
  &ready_for_data_receive, &ready_for_data_send,  &dfu_context.state );
  @ ensures \result == \true <==> (\exists integer i; 0 <= i < 5 && dfu_automaton[current_state].req_trans[i].request == request) && (dfu_context.state == \old(dfu_context.state));
  @ ensures (\forall integer i; 0 <= i < 5 ==>  dfu_automaton[current_state].req_trans[i].request != request) && (dfu_context.state == DFUERROR) ==> (\result == \false) ;
 */
static bool dfu_is_valid_transition(dfu_state_enum_t current_state,
        dfu_request_t    request)
{
  /*@ loop invariant 0 <= i <= 5;
    @ loop invariant \valid_read(dfu_automaton[current_state].req_trans + (0 .. 4));
    @ loop invariant dfu_context.state == \at(dfu_context.state, Pre) ; 
    @ loop invariant (\forall integer prei; 0 <= prei < i ==> dfu_automaton[current_state].req_trans[prei].request != request);
    @ loop assigns i;
    @ loop variant 5-i;
  */
    for (uint8_t i = 0; i < 5; ++i) {
        if (dfu_automaton[current_state].req_trans[i].request == request) {
	  /*@ assert dfu_context.state == \at(dfu_context.state, Pre); */
	  /*@ assert (dfu_automaton[current_state].req_trans[i].request == request);*/
	   /*@ assert \exists integer k; 0 <= k < 5 && dfu_automaton[current_state].req_trans[k].request == request ; */
	  return true;
        }
    }
    /*@ assert (\forall integer i; 0 <= i < 5 ==> dfu_automaton[current_state].req_trans[i].request != request) ; */
    /*@ assert dfu_context.state == \at(dfu_context.state, Pre); */
    /*@ assert dfu_context == \at(dfu_context, Pre); */
    /*
     * Didn't find any request associated to current state. This is not a
     * valid transition. We should fallback to DFUERROR state.
     */
    log_printf("invalid transition from state %d, request %d\n", current_state, request);
    dfu_set_state(DFUERROR);
    /*@ assert dfu_context.state == DFUERROR; */
    /* @ assert (\forall integer i; 0 <= i < 5 ==> dfu_automaton[current_state].req_trans[i].request != request) ; */
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
/*@
  @ assigns \nothing;
 */
static inline void enter_critical_section(void)
{
    uint8_t ret;
    ret = sys_lock (LOCK_ENTER); /* Enter in critical section */
    if(ret != SYS_E_DONE){
        log_printf("Error: failed entering critical section!\n");
    }
    return;
}

/*
 * \brief leaving a critical section
 *
 * Reallow the execution of the previously postponed task ISR.
 */
/*@
  @ assigns \nothing;
 */
static inline void leave_critical_section(void)
{
    uint8_t ret;
    ret = sys_lock (LOCK_EXIT);  /* Exit from critical section */
    if(ret != SYS_E_DONE){
        log_printf("Error: failed exiting critical section!\n");
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
/*@
  @ requires \separated(&GHOST_opaque_drv_privates, &dfu_usb_write_in_progress);
  @ assigns ready_for_data_receive, GHOST_opaque_drv_privates,
            dfu_usb_read_in_progress, dfu_context.data_to_store,
            dfu_usb_write_in_progress, dfu_context.block_in_progress,
            dfu_context.poll_start, dfu_context.poll_timeout_ms;
	    @*/
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
/*@
  @ requires OK <= new_status <= ERRSTALLEDPKT;
  @ assigns ready_for_data_receive, dfu_usb_read_in_progress,
            dfu_context.data_to_store, dfu_usb_write_in_progress,
            dfu_context.block_in_progress, dfu_context.poll_start,
            dfu_context.poll_timeout_ms, GHOST_opaque_drv_privates, dfu_context.status;
  @ ensures dfu_context.status == new_status;
 */
static inline void dfu_error(const dfu_status_enum_t new_status)
{
    log_printf("%s: status=%d\n", __func__, new_status);
    if(new_status == ERRSTALLEDPKT){
        log_printf("stalling...\n");
        dfu_prepare_stall();
        dfu_set_status(new_status);
        return;
    }
    log_printf("state -> Error\n");
    dfu_set_status(new_status);
    request_data_membarrier();
}



/*@
  @ assigns *b;
 */
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
    /* PTH: value on stack, no impact */
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

/*@
  @ behavior not_busy_and_not_load_sync :
        @ assumes dfu_context.state != DFUDNBUSY && dfu_context.state != DFUDNLOAD_SYNC;
        @ assigns \nothing;
 
  @
  @ behavior busy_or_load_sync :
        @ assumes !(dfu_context.state != DFUDNBUSY && dfu_context.state != DFUDNLOAD_SYNC);
        @ assigns dfu_context.data_out_current_block_nb, dfu_context.data_to_store;
        @ ensures dfu_context.data_out_current_block_nb == \old(dfu_context.data_out_current_block_nb)+1 && dfu_context.data_to_store == \false;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/

static void dfu_store_data(void)
{
    dfu_context_t * dfu_ctx = dfu_get_context();

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
    request_data_membarrier();
    return;
}

/*@
  @ behavior null_data:
  @ assumes dfu_context.data_in_buffer == NULL;
  @ assigns \nothing;
  @
  @ behavior notidle:
  @ assumes dfu_context.data_in_buffer != NULL;
  @ assumes dfu_context.state != DFUUPLOAD_IDLE;
  @ assigns \nothing;
  @
  @ behavior idle:
  @ assumes dfu_context.data_in_buffer != NULL;
  @ assumes dfu_context.state == DFUUPLOAD_IDLE;
  @ assigns dfu_context.data_in_current_block_nb;
  @ ensures dfu_context.data_in_current_block_nb ==\old(dfu_context.data_in_current_block_nb) + 1;
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/

static void dfu_load_data(void)
{
    dfu_context_t * dfu_ctx = dfu_get_context();
    /* sanitation for buffers */
    if (dfu_ctx->data_in_buffer == NULL) {
        /* PTH: erroring ? */
        goto err;
    }
    /*@ assert \valid(dfu_ctx->data_in_buffer+(0 .. dfu_ctx->data_in_length-1)); */

    /* INFO: size is given by setup packet but the block number is not
     * managed by the host, which only manage a file size */
    if (dfu_get_state() != DFUUPLOAD_IDLE) {
        /* should not happend out of these two states. In that very case,
         * there is no block in progress as the automaton is not in download
         * mode
         */
        goto err;
    }
    dfu_backend_read(dfu_ctx->data_in_buffer, dfu_ctx->data_in_length);
    // now set the write action as done
    dfu_ctx->data_in_current_block_nb += 1;
    request_data_membarrier();
    /* store request sent, no more data to store by now */
err:
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
/*@
  @ assigns dfu_context.block_in_progress, dfu_context.poll_start, dfu_context.poll_timeout_ms, dfu_context.poll_start;
  @ ensures dfu_context.block_in_progress== 0 && dfu_context.poll_start == 0;
*/
void dfu_store_finished(void)
{
    log_printf("%s\n", __func__);
    dfu_context_t * dfu_ctx = dfu_get_context();
    /*
    Should be updated by the main loop. If upper layer received async IPC
    saying that data has been stored, then update these fields:
    */
    dfu_ctx->block_in_progress = 0;
    dfu_ctx->poll_start = 0;
    request_data_membarrier();
    dfu_set_poll_timeout(0, 0);
}

/*
 * same principle as for the dfu_store_finished. This permit to inform
 * the DFU stack that its buffer has been fullfill with the firware chunk content and
 * can now be sent to the host.
 */
/*@
  @ behavior Ok:
  @ assumes bytes_read < dfu_context.data_in_length;
  @ assigns ready_for_data_receive, GHOST_opaque_drv_privates,
            dfu_usb_read_in_progress, dfu_context.data_to_store,
            dfu_usb_write_in_progress, dfu_context.block_in_progress,
            dfu_context.poll_start, dfu_context.poll_timeout_ms,
            GHOST_in_eps[0].state, dfu_context.data_in_nb_blocks,
	    dfu_context.data_in_length, dfu_context.data_in_current_block_nb,
	    dfu_context.block_in_progress, dfu_context.session_in_progress,
	    dfu_context.state;
  @ ensures dfu_context.state == DFUIDLE;
  @
  @ behavior ko:
  @ assumes bytes_read >= dfu_context.data_in_length;
  @ assigns ready_for_data_receive, GHOST_opaque_drv_privates,
            dfu_usb_read_in_progress, dfu_context.data_to_store,
            dfu_usb_write_in_progress, dfu_context.block_in_progress,
            dfu_context.poll_start, dfu_context.poll_timeout_ms,
            GHOST_in_eps[0].state;

  @ complete behaviors;
  @ disjoint behaviors;
@*/
void dfu_load_finished(uint16_t bytes_read)
{
    dfu_context_t * dfu_ctx = dfu_get_context();

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
        request_data_membarrier();
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
// PMO todo with others behaviors
/*@ behavior notdfundbusy:
        @ assumes dfu_context.state != DFUDNBUSY ;
        @ assigns \nothing; 
  */


static void dfu_handle_dnbusy_timeout(void)
{
    dfu_context_t * dfu_ctx = dfu_get_context();

    #ifdef __FRAMAC__
    //dfu_context.state = DFUDNBUSY ;
    #endif/*!__FRAMAC__*/

    if (dfu_get_state() == DFUDNBUSY) {
        uint64_t ms = 0;
        uint8_t ret;
        ret = sys_get_systick(&ms, PREC_MILLI);
        if (ret != SYS_E_DONE) {
            log_printf("Error: unable to get systick value !\n");
            goto err;
        }
        /* detecting timeout */
        if ((ms - dfu_ctx->poll_start) > dfu_ctx->poll_timeout_ms) {
            dfu_set_state(DFUDNLOAD_SYNC);
        }
    }
    request_data_membarrier();
err:
    return;
}
/* PMO move here to be used in ACSL annotations */
struct queue *dfu_cmd_queue = NULL;
static bool dfu_cmd_queue_empty = true;

/**********************************************
 * Handlers for each request
 *********************************************/

/*
 * Handle DFU_DETACH event
 */

/*@
  @ requires \separated(setup_packet + (..), &GHOST_opaque_libusbdci_privates, &GHOST_num_ctx,
                        (struct __anonstruct_dfu_automaton_83 const *)dfu_automaton + (..),
                        &num_ctx, &dfu_usb_read_in_progress, &dfu_usb_write_in_progress,
                        &ready_for_data_receive, &ready_for_data_send, &dfu_cmd_queue,
                        &dfu_cmd_queue_empty);
  @ assigns dfu_context.state , GHOST_opaque_drv_privates, dfu_usb_write_in_progress, dfu_context.status;
  @ ensures \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE ; 
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
    log_printf("%s: invalid_transition\n", __func__);
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_INVSTATE;

}


/*
 * Handle DFU_DNLOAD event
 */
mbed_error_t dfu_request_dnload(usbctrl_setup_pkt_t *setup_packet)
{
    log_printf("%s\n", __func__);
    dfu_context_t * dfu_ctx = dfu_get_context();
    /* Sanity check */
    if(setup_packet == NULL){
        log_printf("invalid setup pkt NULL\n");
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
                    dfu_ctx->block_size = setup_packet->wLength;
                    dfu_ctx->session_in_progress = 1;
                    log_printf("read %dB\n", dfu_ctx->block_size);
                    set_bool_with_membarrier(&ready_for_data_receive, false);
#if CONFIG_USR_LIB_DFU_DEBUG
                    memset(dfu_ctx->data_out_buffer, 0, dfu_ctx->transfert_size);
#endif
                    /* prepare recv FIFO */
                    dfu_usb_driver_setup_read(dfu_ctx->data_out_buffer, dfu_ctx->block_size);
                    /* and acknowledge host */
                    dfu_usb_driver_setup_send_status(0);
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
                    dfu_ctx->block_size = setup_packet->wLength;
                    set_bool_with_membarrier(&ready_for_data_receive, false);
#if CONFIG_USR_LIB_DFU_DEBUG
                    log_printf("read %dB\n", dfu_ctx->block_size);
                    memset(dfu_ctx->data_out_buffer, 0, dfu_ctx->transfert_size);
#endif
                    dfu_usb_driver_setup_read(dfu_ctx->data_out_buffer, dfu_ctx->block_size);
                    dfu_usb_driver_setup_send_status(0);
                }
                break;
            }
        default:
            log_printf("maybe a missing state: check automaton\n");
            break;
    }
    request_data_membarrier();

    return MBED_ERROR_NONE;

invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_INVSTATE;

    /* FIXME proper error ?*/
download_not_supported:
    log_printf("dfu error: idle and can't download !\n");
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_UNSUPORTED_CMD;

size_too_big:
    log_printf("dfu error ! input size too big! %x > %x\n",
            setup_packet->wLength, dfu_ctx->transfert_size);
    dfu_error(ERRSTALLEDPKT);
    return MBED_ERROR_TOOBIG;
}

/*@
  @ assigns dfu_context.state,ready_for_data_receive, dfu_usb_read_in_progress,
            dfu_context.data_to_store, dfu_usb_write_in_progress,
            dfu_context.block_in_progress, dfu_context.poll_start,
            dfu_context.poll_timeout_ms, GHOST_opaque_drv_privates,
            dfu_context.status;
  @ ensures dfu_context.state == DFUERROR && dfu_context.status == new_status;
*/
void dfu_leave_session_with_error(const dfu_status_enum_t new_status)
{
    dfu_context_t * dfu_ctx = dfu_get_context();
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
    dfu_context_t * dfu_ctx = dfu_get_context();
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
                        set_bool_with_membarrier(&ready_for_data_send, false);
                        log_printf("write %dB @%x\n", dfu_ctx->block_size, dfu_ctx->data_in_nb_blocks);
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
                        set_bool_with_membarrier(&ready_for_data_send, false);
                        dfu_set_state(next_state);
                        /* FIXME block number & size are needed */
                        log_printf("write %dB @%x\n", dfu_ctx->block_size, dfu_ctx->data_in_nb_blocks);
                        dfu_load_data();
                    }
                }
                break;
            }
        default:
            log_printf("maybe a missing state: check automaton\n");
            break;
    }

    request_data_membarrier();
    return MBED_ERROR_NONE;

invalid_transition:
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_INVSTATE;

    /* FIXME proper error ?*/
upload_not_supported:
    log_printf("dfu error ! idle mode and can't upload\n");
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_UNSUPORTED_CMD;

size_too_big:
    log_printf("dfu error ! input size too big! %x > %x\n",
            setup_packet->wLength, dfu_ctx->transfert_size);
    dfu_error(ERRSTALLEDPKT);
    return MBED_ERROR_TOOBIG;
}

/*
 * Handle DFU_GETSTATUS event
 */
mbed_error_t dfu_request_getstatus(usbctrl_setup_pkt_t *setup_packet, uint64_t timestamp)
{
    log_printf("%s\n", __func__);
    dfu_context_t * dfu_ctx = dfu_get_context();
    /* Sanity check */
    if(setup_packet == NULL){
        goto invalid_transition;
    }
    /* Sanity check and next state detection */
    uint8_t next_state;
    /* we use a union here because setup_send is using generic buffer as input (i.e. const uint8_t*) */
    union status_infos_t {
        device_dfu_status_t data;
        uint8_t             buf[sizeof(device_dfu_status_t)];
    };
    union status_infos_t status;

    if (!dfu_is_valid_transition(dfu_get_state(), setup_packet->bRequest)) {
        goto invalid_transition;
    }
    next_state = dfu_next_state(dfu_get_state(), setup_packet->bRequest);


    /* effective transition execution (if needed) */
    switch( dfu_get_state()) {
        case APPIDLE:
            {
                /* staying in APPIDLE */
                status.data.bStatus = dfu_get_status();
                status.data.bwPollTimeout[0] = 0;
                status.data.bwPollTimeout[1] = 0;
                status.data.bwPollTimeout[2] = 0;
                status.data.bState = dfu_get_state();
                status.data.iString = dfu_get_status_string_id();

                dfu_usb_driver_setup_send(&status.buf[0], sizeof(status));
                break;
            }
        case APPDETACH:
            {
                /* staying in APPDETACH */
                status.data.bStatus = dfu_get_status();
                status.data.bwPollTimeout[0] = 0;
                status.data.bwPollTimeout[1] = 0;
                status.data.bwPollTimeout[2] = 0;
                status.data.bState = dfu_get_state();
                status.data.iString = dfu_get_status_string_id();

                dfu_usb_driver_setup_send(&status.buf[0], sizeof(status));
                break;
            }
        case DFUIDLE:
            {
                /* staying in DFUIDLE */
                status.data.bStatus = dfu_get_status();
                status.data.bwPollTimeout[0] = (dfu_get_poll_timeout() >>  0) & 0xFF;
                status.data.bwPollTimeout[1] = (dfu_get_poll_timeout() >>  8) & 0xFF;
                status.data.bwPollTimeout[2] = (dfu_get_poll_timeout() >> 16) & 0xFF;
                status.data.bState = dfu_get_state();
                status.data.iString = dfu_get_status_string_id();

                dfu_usb_driver_setup_send(&status.buf[0], sizeof(status));
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
                status.data.bStatus = dfu_get_status();
                status.data.bwPollTimeout[0] = (dfu_get_poll_timeout() >>  0) & 0xFF;
                status.data.bwPollTimeout[1] = (dfu_get_poll_timeout() >>  8) & 0xFF;
                status.data.bwPollTimeout[2] = (dfu_get_poll_timeout() >> 16) & 0xFF;
                status.data.bState = dfu_get_state();
                status.data.iString = dfu_get_status_string_id();

                /* if a previous DNLOAD is not yet finished, wait before
                 * reconfiguring the USB device
                 */
                dfu_usb_driver_setup_send(&status.buf[0], sizeof(status));
                // XXX pth:
                request_data_membarrier();
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
#if CONFIG_USR_LIB_DFU_DEBUG
                    /* clearly, get_status arise *before* end of timeout !
                     * this is a violation of the DFU automaton */
                    uint32_t ts_low = (uint32_t)timestamp;
                    uint32_t ts_high = (uint32_t)(timestamp >> 32);
                    uint32_t ps_low = (uint32_t)dfu_ctx->poll_start;
                    uint32_t ps_high = (uint32_t)(dfu_ctx->poll_start >> 32);
                    uint32_t pt = (uint32_t)dfu_ctx->poll_timeout_ms;
                    log_printf("error: ts: %x%x ; ps: %x%x pt: %x\n", ts_high, ts_low, ps_high, ps_low, pt);
#endif
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
                status.data.bStatus = dfu_get_status();
                status.data.bwPollTimeout[0] = (dfu_get_poll_timeout() >>  0) & 0xFF;
                status.data.bwPollTimeout[1] = (dfu_get_poll_timeout() >>  8) & 0xFF;
                status.data.bwPollTimeout[2] = (dfu_get_poll_timeout() >> 16) & 0xFF;
                status.data.bState = dfu_get_state();
                status.data.iString = dfu_get_status_string_id();

                /* if a previous DNLOAD is not yet finished, wait before
                 * reconfiguring the USB device
                 */
                dfu_usb_driver_setup_send(&status.buf[0], sizeof(status));
                // XXX pth:
                request_data_membarrier();
                break;
            }

        case DFUDNLOAD_IDLE:
            {
                status.data.bStatus = dfu_get_status();
                status.data.bwPollTimeout[0] = (dfu_get_poll_timeout() >>  0) & 0xFF;
                status.data.bwPollTimeout[1] = (dfu_get_poll_timeout() >>  8) & 0xFF;
                status.data.bwPollTimeout[2] = (dfu_get_poll_timeout() >> 16) & 0xFF;
                status.data.bState = dfu_get_state();
                status.data.iString = dfu_get_status_string_id();

                dfu_usb_driver_setup_send(&status.buf[0], sizeof(status));
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

                status.data.bStatus = dfu_get_status();
                status.data.bwPollTimeout[0] = (dfu_get_poll_timeout() >>  0) & 0xFF;
                status.data.bwPollTimeout[1] = (dfu_get_poll_timeout() >>  8) & 0xFF;
                status.data.bwPollTimeout[2] = (dfu_get_poll_timeout() >> 16) & 0xFF;
                status.data.bState = dfu_get_state();
                status.data.iString = dfu_get_status_string_id();

                dfu_usb_driver_setup_send(&status.buf[0], sizeof(status));
                /* inform the upper layer that the download is complete */
                dfu_backend_eof();
                break;
            }
        case DFUUPLOAD_IDLE:
            {
                /* stays in DFUUPLOAD_IDLE */
                status.data.bStatus = dfu_get_status();
                status.data.bwPollTimeout[0] = (dfu_get_poll_timeout() >>  0) & 0xFF;
                status.data.bwPollTimeout[1] = (dfu_get_poll_timeout() >>  8) & 0xFF;
                status.data.bwPollTimeout[2] = (dfu_get_poll_timeout() >> 16) & 0xFF;
                status.data.bState = dfu_get_state();
                status.data.iString = dfu_get_status_string_id();

                dfu_usb_driver_setup_send(&status.buf[0], sizeof(status));
                break;
            }
        case DFUERROR:
            {
                /* stays in DFUERROR */
                status.data.bStatus = dfu_get_status();
                status.data.bwPollTimeout[0] = (dfu_get_poll_timeout() >>  0) & 0xFF;
                status.data.bwPollTimeout[1] = (dfu_get_poll_timeout() >>  8) & 0xFF;
                status.data.bwPollTimeout[2] = (dfu_get_poll_timeout() >> 16) & 0xFF;
                status.data.bState = dfu_get_state();
                status.data.iString = dfu_get_status_string_id();

                dfu_usb_driver_setup_send(&status.buf[0], sizeof(status));
                break;
            }
        default:
            log_printf("maybe a missing state: check automaton\n");
            break;
    }
    request_data_membarrier();
    return MBED_ERROR_NONE;

invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_INVSTATE;
}



/*
 * Handle DFU_CLEAR_STATUS event
 */
mbed_error_t dfu_request_clrstatus(usbctrl_setup_pkt_t *setup_packet)
{
    dfu_context_t *dfu_ctx = dfu_get_context();
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
    dfu_init_context(dfu_ctx);
    dfu_set_state(next_state);
    dfu_usb_driver_setup_send_status(0);
    request_data_membarrier();
    return MBED_ERROR_NONE;

invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
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

                dfu_usb_driver_setup_send(&state, 1);
                break;
            }
        default:
            log_printf("maybe a missing state: check automaton\n");
            break;
    }
    return MBED_ERROR_NONE;

invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    dfu_error(ERRUNKNOWN);
    return MBED_ERROR_INVSTATE;
}

/*
 * Handle DFU_ABORT event
 */

/*@ assigns dfu_context.state ; */

int dfu_request_abort(usbctrl_setup_pkt_t *setup_packet)
{
    dfu_context_t *dfu_ctx = dfu_get_context();
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
            log_printf("maybe a missing state: check automaton\n");
            break;

    }
    request_data_membarrier();
    return MBED_ERROR_NONE;

invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
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



/******************************************************
 * Global root handler dispatcher (handler mode)
 *
 * This function respond to the various DFU interrupts,
 * in ISR mode. This function only enqueue the various
 * request in order to let the main thread execute these
 * requests and handle the DFU automaton. This ISR function
 * is keeped simple and without any external I/O
 *****************************************************/

/*@
  @ requires \separated(setup_packet + (..), &dfu_context,
  &dfu_usb_read_in_progress, &dfu_usb_write_in_progress,
  &dfu_cmd_queue, &dfu_cmd_queue_empty );
  @
  @ behavior INVPARAM :
  @ assumes setup_packet == 0;
  @ assigns \nothing;
  @ ensures \result == MBED_ERROR_INVPARAM;
  @
  @ behavior OTHERS :
  @ assumes setup_packet != 0;
  @ assigns dfu_usb_read_in_progress, GHOST_opaque_drv_privates, dfu_usb_write_in_progress, dfu_context.status, dfu_cmd_queue, dfu_cmd_queue_empty;
  @ ensures \result == MBED_ERROR_INVCREDENCIALS || \result == MBED_ERROR_UNSUPORTED_CMD || \result == MBED_ERROR_INVPARAM || \result == MBED_ERROR_NOMEM || \result == MBED_ERROR_BUSY || MBED_ERROR_NONE;
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/
#ifndef __FRAMAC__
static
#endif
mbed_error_t dfu_class_parse_request(uint32_t usbdci_handler __attribute__((unused)),
                                            usbctrl_setup_pkt_t *setup_packet)
{
    uint8_t ret;
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint64_t ms = 1;

    /* Sanity check */
    if(setup_packet == NULL){
        log_printf("NULL packet\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    ret = sys_get_systick(&ms, PREC_MILLI);
    if (ret != SYS_E_DONE) {
        log_printf("timestamping error\n");
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
    /* XXX: PTH: really ? even for dnload GetStatus ? they happen during DNLOAD requests not yet written */
    set_bool_with_membarrier(&dfu_usb_read_in_progress, false);

    /*
     * Request unknown (not DFU standard)
     */
    if (setup_packet->bRequest > USB_RQST_DFU_ABORT) {
        log_printf("dfu: %s: unknown request\n", __func__);
        errcode = MBED_ERROR_UNSUPORTED_CMD;
        goto err;
    }

    /*
     * Here we prepare the cell before enqueuing it, The DFU request is queued
     * in order to be executed in main thread mode. The ISR only handle
     * requests enquing
     */
    log_printf("[handler mode] ENQUEUINQ => state %d, req %d\n", dfu_get_state(), setup_packet->bRequest);
    /*@ assert \valid(&cur_req) && sizeof(request_queue_node_t)!=0;*/
    ret = wmalloc((void**)&cur_req, sizeof(request_queue_node_t), ALLOC_NORMAL);
    if (ret != 0) {
        log_printf("Error while allocating queue !!!\n");
        errcode = MBED_ERROR_NOMEM;
        dfu_error(ERRUNKNOWN);
        goto err;
    }

    log_printf("req: %s\n", print_request_name(setup_packet->bRequest));
    cur_req->request = setup_packet->bRequest;
    cur_req->timestamp = ms;
    memcpy((void*)&cur_req->setup_packet, setup_packet, sizeof(usbctrl_setup_pkt_t));
    /*
     * Enqueue and set queue as not empty
     */
    errcode = queue_enqueue(dfu_cmd_queue, cur_req);
    if (errcode == MBED_ERROR_BUSY) {
        log_printf("[ISR] Error! queue is busy!\n");
    }
if (errcode == MBED_ERROR_NOMEM) {
        log_printf("[ISR] Error! queue is full!\n");
    }
    set_bool_with_membarrier(&dfu_cmd_queue_empty, false);

    request_data_membarrier();
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

/*@
  @ requires \separated(current_dfu_cmd + (..), &dfu_context, &dfu_usb_write_in_progress);
  @
  @ behavior KO:
  @ assumes current_dfu_cmd == NULL;
  @ assigns \nothing;
  @
  @ behavior OK:
  @ assumes current_dfu_cmd != NULL;
  @ assigns ready_for_data_receive, dfu_usb_read_in_progress,
            dfu_context.data_to_store, dfu_usb_write_in_progress,
            dfu_context.block_in_progress, dfu_context.poll_start,
            dfu_context.poll_timeout_ms, GHOST_opaque_drv_privates,
            dfu_context.status,*current_dfu_cmd;
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/
static void dfu_release_current_dfu_cmd(request_queue_node_t **current_dfu_cmd)
{
    if(current_dfu_cmd == NULL){
        return;
    }
    if (*current_dfu_cmd != NULL) {
        if (wfree((void**)current_dfu_cmd)) {
            log_printf("freeing current command failed\n");
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
/*PMO todo with other bahaviors */
/*@ behavior ok:
  @ assumes dfu_cmd_queue_empty == true;
  @ assigns \nothing;
  @ ensures \result == MBED_ERROR_NONE ;
  @
  @ behavior ERROR_storage:
  @ assumes dfu_cmd_queue_empty != true;
  @ assumes !\valid(dfu_cmd_queue) ||  dfu_cmd_queue->lock == 0 || dfu_cmd_queue->size == 0 ;
  @ assigns \nothing;
  @ ensures \result == MBED_ERROR_NOSTORAGE;
  @
  @ complete behaviors;
  @ disjoint behaviors;
 */
static mbed_error_t dfu_class_execute_request(void)
{
    request_queue_node_t *current_dfu_cmd_p = NULL;
    request_queue_node_t current_dfu_cmd;
    mbed_error_t         ret = MBED_ERROR_NONE;
    if(dfu_cmd_queue_empty == true)
    {
       /*@ assert dfu_cmd_queue_empty == true ;*/
        return MBED_ERROR_NONE;
    }
    /*@ assert dfu_cmd_queue_empty != true ;*/
    enter_critical_section();
    if (queue_dequeue(dfu_cmd_queue, (void**)&current_dfu_cmd_p) != MBED_ERROR_NONE) {
      /*@ assert !\valid(dfu_cmd_queue) || !\valid(current_dfu_cmd_p) || dfu_cmd_queue->lock == 0 || dfu_cmd_queue->size == 0 ; */
      log_printf("Unable to dequeue command!\n");
      leave_critical_section();
      return MBED_ERROR_NOSTORAGE;
    }

    current_dfu_cmd = *current_dfu_cmd_p;
    dfu_release_current_dfu_cmd(&current_dfu_cmd_p);
    if(queue_is_empty(dfu_cmd_queue)) {
        set_bool_with_membarrier(&dfu_cmd_queue_empty, true);
    }
    leave_critical_section();
#if CONFIG_USR_LIB_DFU_DEBUG
    dfu_state_enum_t old_state;
    old_state = dfu_get_state();
    printf("[main thread] DEQUEUING, state is: %d\n", old_state);
#endif
    switch (current_dfu_cmd.setup_packet.bRequest) {
	/* Note: (void*) cast to silence clang [-Werror,-Waddress-of-packed-member]
	 * Our architecture allows unaligned accesses, so this should be OK.
	 */
        case USB_RQST_DFU_DETACH:
            log_printf("DFU_DETACH\n");
            if((ret = dfu_request_detach((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet)))) {
                goto err;
            }
            break;

        case USB_RQST_DFU_DNLOAD:
            log_printf("DFU_DNLOAD\n");
            if((ret = dfu_request_dnload((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet)))) {
                goto err;
            }
            break;

        case USB_RQST_DFU_UPLOAD:
            log_printf("DFU_UPLOAD\n");
            if((ret = dfu_request_upload((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet)))) {
                goto err;
            }
            break;

        case USB_RQST_DFU_GET_STATUS:
            log_printf("DFU_GET_STATUS\n");
            if((ret = dfu_request_getstatus((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet), current_dfu_cmd.timestamp))) {
                goto err;
            }
            break;

        case USB_RQST_DFU_CLEAR_STATUS:
            log_printf("DFU_CLEAR_STATUS\n");
            if((ret = dfu_request_clrstatus((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet)))) {
                goto err;
            }
            break;

        case USB_RQST_DFU_GET_STATE:
            log_printf("DFU_GET_STATE\n");
            if((ret = dfu_request_getstate((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet)))) {
                goto err;
            }
            break;

        case USB_RQST_DFU_ABORT:
            log_printf("DFU_GET_ABORT\n");
            if((ret = dfu_request_abort((usbctrl_setup_pkt_t*)((void*)&current_dfu_cmd.setup_packet)))) {
                goto err;
            }
            break;

        default:
            log_printf("dfu: %s: unknown request %d\n", __func__, current_dfu_cmd.setup_packet.bRequest);
            dfu_error(ERRUNKNOWN);
    }
#if CONFIG_USR_LIB_DFU_DEBUG
    new_state = dfu_get_state();
    log_printf("[XXX] WE HAVE TRANSITIONED FROM %s to %s, the request was %s\n", print_state_name(old_state), print_state_name(new_state), print_request_name(current_dfu_cmd.setup_packet.bRequest));
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
#ifndef __FRAMAC__
static
#endif
/*@ assigns ready_for_data_receive, dfu_usb_read_in_progress, dfu_context.data_to_store;
  @ ensures \result == MBED_ERROR_NONE && ready_for_data_receive == \true 
  && dfu_usb_read_in_progress ==\false && dfu_context.data_to_store == \true; 
*/
mbed_error_t dfu_data_out_handler(uint32_t dev_id __attribute__((unused)),
                                  uint32_t size __attribute__((unused)),
                                  uint8_t ep_id __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dfu_context_t * dfu_ctx = dfu_get_context();
    log_printf("end of USB read\n");
    /* FIXME: size passed here should be checked in comparison with
     * the size passed in the previous request */

    /* all data received from host. This handler is executed by the lower
     * USB stack at the end of the effective usb_status_read() call.
     * Here, we set a flag to request the main thread to effetively copy the
     * buffer content into the flash. When this is done, the flag is
     * lowered and the block_in_pogress field of the dfu context is set to 0.
     */
     set_bool_with_membarrier(&ready_for_data_receive, true);
     set_bool_with_membarrier(&dfu_usb_read_in_progress, false);
     set_bool_with_membarrier(&dfu_ctx->data_to_store, true);
     return errcode;
}

/*
 * Data in handler, called by the USB stack when the task's fifo has been
 * fully read by the USB device in its own FIFO and sent to the host.
 */
#ifndef __FRAMAC__
static
#endif
/*@ assigns dfu_usb_write_in_progress, dfu_context.block_in_progress, dfu_context.poll_start,dfu_context.poll_timeout_ms,dfu_context.poll_start ;
  @ ensures \result == MBED_ERROR_NONE && dfu_usb_write_in_progress == \false; */
mbed_error_t dfu_data_in_handler(uint32_t dev_id __attribute__((unused)),
                                        uint32_t size __attribute__((unused)),
                                        uint8_t ep_id __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dfu_context_t * dfu_ctx = dfu_get_context();
    log_printf("[ISR] end of USB write\n");
    /* USB IP write access is now finished */
    set_bool_with_membarrier(&dfu_usb_write_in_progress, false);

    if (dfu_get_state() == DFUUPLOAD_IDLE) {
        /* The write action on the USB output fifo is finished
         * In DFUUPLOAD mode, this means that the flash data has
         * been successfully pushed into the device and we can handle
         * the next chunk
         */
        dfu_ctx->block_in_progress = 0;
        dfu_ctx->poll_start = 0;
        dfu_set_poll_timeout(0, 0);
        request_data_membarrier();
    }
     return errcode;
}


/****************************************************
 * DFU automaton main call
 **************************************************/
// PMO to be continued
/*@
  @ requires \separated(dfu_cmd_queue, &dfu_cmd_queue_empty);
  @ requires \valid(dfu_cmd_queue);
  @
  @ behavior ok:
  @ assumes dfu_context.data_to_store != \true ;
  @ assigns \nothing ;
  @ ensures \result==MBED_ERROR_NONE ;
  @
  @ behavior ko:
  @ assumes dfu_context.data_to_store != \true ;
  @ assigns \nothing;
  @ ensures \true ;
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/
mbed_error_t dfu_exec_automaton(void)
{
    dfu_context_t * dfu_ctx = dfu_get_context();
    mbed_error_t errcode = MBED_ERROR_NONE;
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
    if (errcode == dfu_class_execute_request()) {
        goto err;
    }
err:
    return errcode;
}


/****************************************************
 * Init functions
 **************************************************/

/*@ assigns dfu_context ;*/
mbed_error_t dfu_declare(uint32_t usbdci_handler)
{
    /* Register our callbacks */
    ADD_LOC_HANDLER(dfu_data_out_handler)
    ADD_LOC_HANDLER(dfu_data_in_handler)
    ADD_LOC_HANDLER(dfu_class_parse_request)
    ADD_LOC_HANDLER(dfu_get_descriptor)

    dfu_context_t * dfu_ctx = dfu_get_context();
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

/*@
  @ requires \separated(buffer + (..), &dfu_cmd_queue);
  @ assigns dfu_context.data_out_buffer, dfu_context.data_in_buffer, dfu_context.block_size, dfu_context.transfert_size, dfu_cmd_queue;*/
//PMO functional part not done
mbed_error_t dfu_init(uint8_t *buffer,
                      uint16_t max_size)
{

    dfu_context_t *dfu_ctx = dfu_get_context();
    mbed_error_t err;
#ifdef CONFIG_STD_MALLOC_LIGHT
    wmalloc_init();

    err = queue_create(MAX_DFU_CMD_QUEUE_SIZE, &dfu_cmd_queue);
    if (err != MBED_ERROR_NONE) {
        log_printf("Unable to create queue !\n");
        return err;
    }
#endif

    log_printf("Initializing DFU Layer\n");
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
        log_printf("max_size %x is invalid\n", max_size);
    }
    dfu_ctx->data_out_buffer = buffer;
    dfu_ctx->data_in_buffer = buffer;
    dfu_ctx->block_size = 0;
    dfu_ctx->transfert_size = max_size;
    return MBED_ERROR_NONE;
}

mbed_error_t dfu_reinit(void)
{
    dfu_context_t *dfu_ctx = dfu_get_context();
    /* effective transition execution (if needed) */
    dfu_init_context(dfu_ctx);
    dfu_set_state(DFUIDLE);
    return MBED_ERROR_NONE;
}

#ifdef __FRAMAC__
/* PMO */
void fcpmo(void){
  dfu_cmd_queue_empty=Frama_C_interval_b(0, 1);
  queue_create(MAX_DFU_CMD_QUEUE_SIZE, &dfu_cmd_queue);
  dfu_usb_driver_setup_send_zlp();
}
#endif
