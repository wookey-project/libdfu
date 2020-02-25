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
#ifndef LIBDFU_H
#define LIBDFU_H

#include "libc/types.h"
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "libc/regutils.h"
#include "libusbctrl.h"

#define MAX_DFU_CMD_QUEUE_SIZE 8

/* Maximum poll timeout for the host to send get_status()
 * requests (in milliseconds).
 */
#define MAX_POLL_TIMEOUT 450

typedef enum dfu_status_enum {
    OK              = 0x00,
    ERRTARGET       = 0x01,
    ERRFILE         = 0x02,
    ERRWRITE        = 0x03,
    ERRERASE        = 0x04,
    ERRCHECK_ERASED	= 0x05,
    ERRPROG         = 0x06,
    ERRVERIFY       = 0x07,
    ERRADDRESS      = 0x08,
    ERRNOTDONE      = 0x09,
    ERRFIRMWARE     = 0x0A,
    ERRVENDOR       = 0x0B,
    ERRUSBR         = 0x0C,
    ERRPOR          = 0x0D,
    ERRUNKNOWN      = 0x0E,
    ERRSTALLEDPKT   = 0x0F,
} dfu_status_enum_t;


/*****************************************************
 * externally supplied implementations prototypes
 *
 * WARNING: these functions MUST be defined in the binary
 * which include the libDFU. These functions implement
 * the backend storage access, which may vary depending on
 * the overall system implementation and which is not, as a
 * consequence, a DFU specific implementation.
 *****************************************************/

/*
 * Why using symbol resolution instead of callbacks ?
 *
 * Symbol resolution is made at link time, instead of requiring
 * function pointers that need to be registered in a writable
 * area of the application memory.
 *
 * A lot of security vulnerabilities are based on function pointers
 * corruption using overflows on stack contexts, making ROP or
 * any other uncontrolled execution flows possible.
 *
 * Moreover, linking directly to the symbol avoid a resolution of
 * the callback address and help the compiler at optimization time.
 */

/*
 * \brief Write data to the storage backend
 *
 * \param data      the data buffer pointer
 * \param data_size the size (in bytes) to write
 * \param blocknum  the DFU block identifier
 *
 * \return 0 on success
 */
uint8_t dfu_backend_write(uint8_t ** volatile data,
                          const uint16_t      data_size,
                          uint16_t            blocknum);

/*
 * \brief Read data from the storage backend
 *
 * \param data      the data buffer pointer
 * \param data_size the size (in bytes) to read
 *
 * \return 0 on success
 */
uint8_t dfu_backend_read(uint8_t *data, uint16_t data_size);

/*
 * \brief Inform storage backend that there is no more content to write
 *
 * This function is used in DFU DNWLOAD mode only
 *
 */
void dfu_backend_eof(void);

/*
 * \brief respond to a reset has been received on the line
 *
 * When a reset has been received on control endpoint while the DFU state
 * machine is running, this means that something bad happened. The policy to
 * handle this reset softly, or hardly (for e.g. by rebooting) is leaving
 * to the user task, depending on the global device software stack.
 *
 * This function is triggered only *after* the enumeration phase, until the
 * DFU stack is up and running.
 *
 */
void dfu_reset_device(void);



/***********************************************************
 * libDFU API
 ***********************************************************/

void dfu_leave_session_with_error(const dfu_status_enum_t new_status);

/*
 * Early initialization, declaring the DFU stack.
 * This *does not* include the USB stack initialisation as the libctrl
 * initalization is under the responsability of the upper layer (hybrid device
 * typical case).
 */
mbed_error_t dfu_declare(usbctrl_context_t *usb_ctx);

/**
 * @brief initialize the DFU stack
 *
 * @param buffer   the data buffer to use for storing data from/to USB FIFO
 * @param max_size the buffer size, at least 64, must be a power of 2.
 */
mbed_error_t dfu_init(uint8_t **buffer,
                      uint16_t max_size);


/*
 * DFU stack RaZ (except for libusbctrl declarations), typically for
 * USB reset trigger
 */
mbed_error_t dfu_reinit(void);
/**
 * Run the DFU automaton.
 * This is *not* a loop, as the task may require to support, in the same loop,
 * external events, such as IPC. The task has to handle the loop, using a
 * block such as:
 * while (1) {
 *   dfu_exec_automaton();
 *   if (sys_ipc(IPC_RECV_ASYNC, &id, &buf) == SYS_E_DONE) {
 *     // handle IPC request
 *   }
 * }
 */
mbed_error_t dfu_exec_automaton(void);

/*
 * The storing backend has finished to store data ? This function inform the
 * DFU that it can leave the DNLOAD_SYNC/DNBUSY couple.
 */
void dfu_store_finished(void);

/*
 * The loading backend has finished to load data ? This function inform the
 * DFU that it can send the buffer content into the USB device output FIFO
 */
void dfu_load_finished(uint16_t bytes_read);

#endif/*!LIBDFU_H*/
