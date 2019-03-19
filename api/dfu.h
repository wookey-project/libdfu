#ifndef _USB_DFU_UTILS_H
#define _USB_DFU_UTILS_H

#include "api/types.h"
#include "api/stdio.h"
#include "api/nostd.h"
#include "api/regutils.h"
#include "usb.h"
/* usb driver control header */
#include "usb_control.h"

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


/***********************************************************
 * libDFU API
 ***********************************************************/

void dfu_leave_session_with_error(const dfu_status_enum_t new_status);

/*
 * Early initialization, declaring the DFU stack. This include the USB
 * stack initialisation. This function must be called before the
 * sys_init(INIT_DONE) call.
 * Request PERM_RES_DEV_BUSES permission.
 * CAUTION: in USB-HS mode, the task must have the MAP_VOLUNTARY permission
 */
void dfu_early_init(void);

/**
 * @brief initialize the DFU stack
 *
 * @param buffer   the data buffer to use for storing data from/to USB FIFO
 * @param max_size the buffer size, at least 64, must be a power of 2.
 */
void dfu_init(uint8_t **buffer,
              uint16_t max_size);

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
void dfu_exec_automaton(void);

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

#endif
