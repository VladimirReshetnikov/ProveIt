"""Canonical gzip container for newly authored fixed-coefficient payloads.

The header is fixed rather than inherited from the host/Python gzip wrapper:
no optional fields, MTIME=0, XFL=2 (maximum compression), OS=3 by convention.
OS=3 is an encoding convention, not a report of the executing host platform.
Reference byte reproduction: CPython 3.12.14, zlib 1.3.2, level 9, memLevel 8,
default strategy. Decoded coefficient bytes have their own independent hashes.
"""
import struct
import zlib

HEADER=bytes.fromhex('1f8b0800000000000203')

def canonical_gzip(raw):
    compressor=zlib.compressobj(
        level=9,method=zlib.DEFLATED,wbits=-zlib.MAX_WBITS,
        memLevel=8,strategy=zlib.Z_DEFAULT_STRATEGY)
    body=compressor.compress(raw)+compressor.flush()
    trailer=struct.pack('<II',zlib.crc32(raw)&0xffffffff,len(raw)&0xffffffff)
    return HEADER+body+trailer
