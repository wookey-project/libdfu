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

#ifndef DFU_CONTEXT_H_
#define DFU_CONTEXT_H_

#include "autoconf.h"
#include "libc/types.h"

/*
 * DFU context
 * TODO: fields should be ordered more cleanly, depending on their:
 * 1) usage
 * 2) size per usage
 * for a better readability
 */
typedef struct  {
    uint8_t               block_in_progress;
    uint8_t               session_in_progress;
    dfu_state_enum_t      state;
    dfu_status_enum_t     status;
    uint16_t              data_out_nb_blocks;
    uint32_t              data_out_length;
    uint16_t              data_in_nb_blocks;
    uint32_t              data_in_length;
    uint32_t              flash_address;
    uint16_t              detach_timeout_ms;
    uint64_t              detach_timeout_start;
    uint16_t              poll_timeout_ms;
    uint64_t              poll_start;
    uint16_t              block_size;
    uint16_t              transfert_size;
    uint32_t              firmware_size;
    uint8_t **            data_out_buffer;
    uint8_t **            data_in_buffer;
    uint16_t              data_out_current_block_nb;
    uint16_t              data_in_current_block_nb;
    uint32_t              current_block_offset;
    bool                  data_to_store;
    bool                  data_to_load;
    bool                  can_download;
    bool                  can_upload;
    usbctrl_interface_t   iface;
} dfu_context_t;

void dfu_init_context(dfu_context_t *ctx);

dfu_context_t * dfu_get_context(void);

#ifdef __FRAMAC__
dfu_context_t dfu_context = {0};
#endif

#endif /*!DFU_CONTEXT_H_*/
