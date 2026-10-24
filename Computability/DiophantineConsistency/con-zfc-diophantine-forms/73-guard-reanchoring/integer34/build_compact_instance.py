#!/usr/bin/env python3
"""Bind the unchanged symbolic sextic to the complete compact source44 tuple."""
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
packet=json.loads((HERE/'sextic34.json').read_text())
packet['name']='sextic34_transport_pivot_compact'
packet['coefficient_binding']={
    'backend':'wang943-complement67-shared-anchor-length8807-prime581197',
    'manifest':'../compact_coefficients/native/COEFFICIENT_BINDING.json',
    'ports':{
        'beta':'../compact_coefficients/native/coefficients/beta.bin.gz',
        'K0':'../compact_coefficients/native/coefficients/K.bin.gz',
        'MC':'../compact_coefficients/native/coefficients/MC.bin.gz',
        'MF':'../compact_coefficients/native/coefficients/MF_source.bin.gz'
    },
    'format':'gzip of minimal unsigned little-endian integer bytes',
    'beta':'2^590069-1',
    'mask_convention':'MF is already shifted by beta',
    'policy':'Use the complete compact source44 tuple; the source34 instance remains separately bound.',
    'adapter':'COMPACT_S34_ADAPTER.md'
}
packet['proof_status']='Exact symbolic local reduction plus ordinary complete compact-tuple adapter; no new end-to-end formal certificate.'
(HERE/'sextic34_compact.json').write_text(json.dumps(packet,indent=2)+'\n')
print('Wrote separately bound compact instance; residuals, unknowns and degree unchanged.')
