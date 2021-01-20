#include "api/dfu.h"
#include "autoconf.h"
#include "libc/types.h"
#include "libc/string.h"
//#include <string.h>
#include "libusbctrl.h"
#include "dfu_priv.h"
#include "framac/entrypoint.h"

/*
 * Support for Frama-C testing
 */

//@ assigns Frama_C_entropy_source_b \from Frama_C_entropy_source_b;
void Frama_C_update_entropy_b(void) {
  Frama_C_entropy_source_b = Frama_C_entropy_source_b;
}


//@ assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
void Frama_C_update_entropy_8(void) {
  Frama_C_entropy_source_8 = Frama_C_entropy_source_8;
}

//@ assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
void Frama_C_update_entropy_16(void) {
  Frama_C_entropy_source_16 = Frama_C_entropy_source_16;
}

//@ assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
void Frama_C_update_entropy_32(void) {
  Frama_C_entropy_source_32 = Frama_C_entropy_source_32;
}


/*@ requires order: 0 <= min <= max <= 1;
    assigns \result \from min, max, Frama_C_entropy_source_b;
    assigns Frama_C_entropy_source_b \from Frama_C_entropy_source_b;
    ensures result_bounded: min <= \result <= max ;
 */

bool Frama_C_interval_b(bool min, bool max)
{
  bool r,aux;
  Frama_C_update_entropy_b();
  aux = Frama_C_entropy_source_b;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}



/*@ requires order: 0 <= min <= max <= 255;
    assigns \result \from min, max, Frama_C_entropy_source_8;
    assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
    ensures result_bounded: min <= \result <= max ;
 */

uint8_t Frama_C_interval_8(uint8_t min, uint8_t max)
{
  uint8_t r,aux;
  Frama_C_update_entropy_8();
  aux = Frama_C_entropy_source_8;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*@ requires order: 0 <= min <= max <= 65535;
    assigns \result \from min, max, Frama_C_entropy_source_16;
    assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
    ensures result_bounded: min <= \result <= max ;
 */

uint16_t Frama_C_interval_16(uint16_t min, uint16_t max)
{
  uint16_t r,aux;
  Frama_C_update_entropy_16();
  aux = Frama_C_entropy_source_16;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*@ requires order: 0 <= min <= max <= 4294967295;
    assigns \result \from min, max, Frama_C_entropy_source_32;
    assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
    ensures result_bounded: min <= \result <= max ;
 */

uint32_t Frama_C_interval_32(uint32_t min, uint32_t max)
{
  uint32_t r,aux;
  Frama_C_update_entropy_32();
  aux = Frama_C_entropy_source_32;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*

 test_fcn_usbctrl : test des fonctons définies dans usbctrl.c avec leurs paramètres
 					correctement définis (pas de débordement de tableaux, pointeurs valides...)

*/

#define USB_BUF_SIZE 4096

uint8_t recv_buf[USB_BUF_SIZE];

void test_fcn_dfu(){

/*
    def d'une nouvelle interface pour test de la fonction usbctrl_declare_interface
    Déclaration d'une structure usb_rqst_handler_t utilisée dans les interfaces, qui nécessite aussi une structure usbctrl_setup_pkt_t
*/


    uint32_t ctxh1=0;
    uint32_t ctxh2=0;
    uint8_t  hid_handler;
    mbed_error_t errcode;



    ///////////////////////////////////////////////////
    //        premier context
    ///////////////////////////////////////////////////

    usbctrl_declare(8, &ctxh1);  // in order to check dev_id !=6 and != 7 ;
    usbctrl_declare(6, &ctxh1);
    /*@ assert ctxh1 == 0 ; */
    usbctrl_initialize(ctxh1);
    /*@ assert ctxh1 == 0 ; */

    errcode = dfu_declare(ctxh1);

    dfu_init((uint8_t**)&recv_buf, USB_BUF_SIZE);

    usbctrl_start_device(ctxh1);

    usbctrl_setup_pkt_t setup = { 0 };

    uint8_t dfu_req_tab[] = {
        USB_RQST_DFU_GET_STATUS,
        USB_RQST_DFU_GET_STATE,
        USB_RQST_DFU_DNLOAD,
        USB_RQST_DFU_DNLOAD,
        USB_RQST_DFU_GET_STATUS,
        USB_RQST_DFU_DNLOAD,
        USB_RQST_DFU_GET_STATE,
        USB_RQST_DFU_DNLOAD,
        USB_RQST_DFU_GET_STATUS,
        //USB_RQST_DFU_UPLOAD,
        USB_RQST_DFU_CLEAR_STATUS,
        USB_RQST_DFU_ABORT,
        USB_RQST_DFU_GET_STATUS,
        USB_RQST_DFU_DETACH,
        USB_RQST_DFU_GET_STATUS,
    };
    uint8_t dfu_req_tab_len = sizeof(dfu_req_tab)/sizeof(uint8_t);

    for (uint8_t i = 0; i < dfu_req_tab_len; ++i) {

        dfu_exec_automaton();

        // 1. set buffer with content
        // 2. call handler
        setup.bRequest = dfu_req_tab[i];
        if (dfu_req_tab[i] == USB_RQST_DFU_DNLOAD) {
            /* specify that 4K is to be read from host in current URB */
            setup.wValue = 8;
            setup.wLength = USB_BUF_SIZE;
        }
        if (dfu_req_tab[i] == USB_RQST_DFU_UPLOAD) {
            /* specify that 4K is to be send to the host in current URB */
            setup.wValue = 8;
            setup.wLength = USB_BUF_SIZE;
        }
        //  DFU command recv on EP0
        dfu_class_parse_request(0, &setup);
        // exec DFU command
        dfu_exec_automaton();
        if (dfu_req_tab[i] == USB_RQST_DFU_DNLOAD) {
            // now that EP0 is ready to recv data, emulate data received trigger
            // data to be read from host, consider data received
            dfu_data_out_handler(0,0,0);
            // handle backend store execution
            dfu_exec_automaton();
            // ... emulate backend acknowledge
            dfu_store_finished();
        }
        if (dfu_req_tab[i] == USB_RQST_DFU_UPLOAD) {
            // emulate backend has finished to store data to DFU buffer
            dfu_load_finished(USB_BUF_SIZE);
            // now that EP0 is ready to send data, emulate data sent trigger
            dfu_data_in_handler(0,0,0);
        }
        // set load event as finished
    }

    dfu_reinit();

    dfu_leave_session_with_error(ERRFILE);

}

/*

 test_fcn_erreur : test des fonctons définies dans usbctrl.c afin d'atteindre les portions de code défensif
                    (pointeurs nulls, débordement de tableaux...)

*/

void test_fcn_dfu_fuzz(){

    usbctrl_setup_pkt_t setup = { 0 };
    setup.bRequest =  Frama_C_interval_8(USB_RQST_DFU_DETACH,0x10); /* request including invalid requests */
    /* Beware: the below code make EVA execution clearly longer. Although, it permits to check the overall$
     * input values (that can be forged by the host) possibilities */
    setup.wValue =  Frama_C_interval_16(0,65535); /* request including invalid requests */
    setup.wLength =  Frama_C_interval_16(0,65535); /* request including invalid requests */

    dfu_class_parse_request(0, &setup);
    dfu_exec_automaton();

    if (setup.bRequest == USB_RQST_DFU_DNLOAD) {
        dfu_store_finished();
        dfu_exec_automaton();
    }
    if (setup.bRequest == USB_RQST_DFU_UPLOAD) {
        dfu_load_finished(USB_BUF_SIZE);
        dfu_exec_automaton();
    }
}

void test_fcn_dfu_erreur(){
}

void test_fcn_driver_eva(){
}

void main(void)
{

    test_fcn_dfu() ;
    dfu_reinit();
    test_fcn_dfu_fuzz();
    test_fcn_dfu_erreur() ;
    test_fcn_driver_eva() ;

}
