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
/** @file usb_device.h
 * \brief Contains usb descriptors
 */
#ifndef _USB_DEVICE_H
#define _USB_DEVICE_H

/* Strings */
#define MAX_DESC_STRING_SIZE		32
#define LANGUAGE_ENGLISH		0x0409

#define STRING_MANUFACTURER		"ANSSI"
#define STRING_MANUFACTURER_INDEX	1
#define STRING_PRODUCT			"Wookey"
#define STRING_PRODUCT_INDEX		2
#define STRING_SERIAL			"123456789012345678901234"
#define STRING_SERIAL_INDEX		3

#define ID_VENDOR           0xDEAD
#define ID_PRODUCT          0xCAFE

#endif
