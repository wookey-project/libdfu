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
/** @file usb_desc.h
 * \brief Contains usb descriptors
 */
#ifndef _DFU_DESC_H
#define _DFU_DESC_H

#include "libc/types.h"
#include "autoconf.h"
#include "libusbctrl.h"

/* Classes, subclasses and protocols for DFU Runtime */
#define USB_NB_INTERFACE        1

#define USB_DESC_DFU_FUNC   0x21

#define USB_CLASS_DFU		0xFE
#define USB_SUBCLASS_DFU	0x01
#define USB_PROTOCOL_DFU_RTM	0x01
#define USB_PROTOCOL_DFU_DFU	0x02
#define DFU_DETACH_TIMEOUT      1000 /* in miliseconds */

/*
 * DFU Class handle a class-level descriptor, named DFU class functional
 * descriptor. This descriptor is return on GetConfiguration, at interface
 * enumeration, using the below callback.
 */
typedef struct __packed {
    uint8_t bLength;
    uint8_t bDescriptorType;
    struct {
        uint8_t bitCanDnload:1;
        uint8_t bitCanUpload:1;
        uint8_t bitManifestationTolerant:1;
        uint8_t bitWillDetach:1;
        uint8_t reserved:4;
    } bmAttributes;
    uint16_t wDetachTimeOut;
    uint16_t wTransferSize;
    uint16_t bcdDFUVersion;
} dfu_class_functional_descriptor_t;


/**
 * \brief Configuration descriptor
 *
 */
mbed_error_t      dfu_get_descriptor(uint8_t             iface_id __attribute__((unused)),
                                     uint8_t            *buf,
                                     uint32_t           *desc_size,
                                     uint32_t            usbdci_handler __attribute__((unused)));
#endif /* !_DFU_DESC_H */

