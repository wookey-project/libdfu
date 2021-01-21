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

#include "libc/types.h"
#include "autoconf.h"
#include "dfu_priv.h"
#include "dfu_context.h"
#include "dfu_desc.h"

/*
 * Returns the DFU class descriptor, named, for DFU functional descriptor.
 * This functions respects the libusbctrl class level descriptor getter API,
 * as defined in libusbctrl.h.
 */
/*@
  @ requires \separated(&dfu_context, buf+(0..*desc_size-1),desc_size);
  @ assigns *desc_size;
  @ assigns buf[0 .. sizeof(dfu_class_functional_descriptor_t)-1];

  @ behavior invparam:
  @   assumes (buf == NULL || desc_size == NULL);
  @   ensures \result == MBED_ERROR_INVPARAM;

  @ behavior nomem:
  @   assumes (buf != NULL && desc_size != NULL);
  @   assumes *desc_size < sizeof(dfu_class_functional_descriptor_t);
  @   ensures \result == MBED_ERROR_NOMEM;

  @ behavior ok:
  @   assumes (buf != NULL && desc_size != NULL);
  @   assumes *desc_size >= sizeof(dfu_class_functional_descriptor_t);
  @   ensures \result == MBED_ERROR_NONE;

  @ complete behaviors;
  @ disjoint behaviors;

  */
mbed_error_t      dfu_get_descriptor(uint8_t             iface_id __attribute__((unused)),
                                     uint8_t            *buf,
                                     uint8_t            *desc_size,
                                     uint32_t            usbdci_handler __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dfu_context_t *dfuctx = dfu_get_context();

    /* DFU CLASS does not support multiple DFU interfaces in the same time,
     * iface_id is ignored */
    /* sanitation */
    if (buf == NULL || desc_size == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (*desc_size < sizeof(dfu_class_functional_descriptor_t)) {
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }
    dfu_class_functional_descriptor_t *desc =
        (dfu_class_functional_descriptor_t *)(&buf[0]);

    /* let's configure fonctionnal desc */
    desc->bLength = sizeof(dfu_class_functional_descriptor_t);
    desc->bDescriptorType                       = USB_DESC_DFU_FUNC;
    desc->bmAttributes.reserved                 = 0;
    desc->bmAttributes.bitWillDetach            = 0;
    desc->bmAttributes.bitManifestationTolerant = 0;
#if CONFIG_USR_LIB_DFU_CAN_UPLOAD
    desc->bmAttributes.bitCanUpload             = 1;
#else
    desc->bmAttributes.bitCanUpload             = 0;
#endif
#if CONFIG_USR_LIB_DFU_CAN_DOWNLOAD
    desc->bmAttributes.bitCanDnload             = 1;
#else
    desc->bmAttributes.bitCanDnload             = 0;
#endif
    desc->wDetachTimeOut                        = DFU_DETACH_TIMEOUT;
   /* Big transfer size chunks */
    desc->wTransferSize                         = dfuctx->transfert_size;
   /* DFU 1.1 */
    desc->bcdDFUVersion = 0x0110;

    *desc_size = sizeof(dfu_class_functional_descriptor_t);
err:
    return errcode;
}
