#include "api/dfu.h"
#include "autoconf.h"
#include "libc/types.h"
#include "libc/string.h"
//#include <string.h>
#include "libusbctrl.h"
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

void usbhid_report_sent_trigger(uint8_t hid_handler,
                                       uint8_t index) {
    hid_handler = hid_handler;
    index = index;
    return;
}

mbed_error_t usbhid_request_trigger(uint8_t hid_handler,
                                    uint8_t hid_req) {
    hid_handler = hid_handler;
    hid_req = hid_req;
    /* FIXME: replace with interval on mbed_error_t */
    return MBED_ERROR_NONE;
}

mbed_error_t usbhid_report_received_trigger(uint8_t hid_handler,
                                            uint16_t size) {
    hid_handler = hid_handler;
    size = size;
    /* FIXME: replace with interval on mbed_error_t */
    return MBED_ERROR_NONE;
}

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



    dfu_exec_automaton();

    dfu_reinit();

    dfu_load_finished(USB_BUF_SIZE);

    dfu_store_finished();


    dfu_leave_session_with_error(ERRFILE);

}

/*

 test_fcn_erreur : test des fonctons définies dans usbctrl.c afin d'atteindre les portions de code défensif
                    (pointeurs nulls, débordement de tableaux...)

*/

void test_fcn_dfu_erreur(){
}

void test_fcn_driver_eva(){
}

void main(void)
{

    test_fcn_dfu() ;
    test_fcn_dfu_erreur() ;
    test_fcn_driver_eva() ;

}
