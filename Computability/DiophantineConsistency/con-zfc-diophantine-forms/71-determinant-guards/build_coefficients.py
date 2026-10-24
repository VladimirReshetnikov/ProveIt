#!/usr/bin/env python3
"""Reconstruct the complete fixed tuple and the new determinant-guard scales."""
from pathlib import Path
import gzip
import hashlib
import importlib.util
import json

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    source = ROOT/'coefficients/source34_builder.py'
    data = source.read_bytes()
    blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    require(blob == 'b85e416b8a8b823c01c8ecacd85eebef7f5c69b5', 'unaltered source34 builder')
    spec = importlib.util.spec_from_file_location('native34', source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    ports, audit = module.construct()
    binding = json.loads((ROOT/'coefficients/source34_binding.json').read_text())
    for key, value in ports.items():
        raw = value.to_bytes((value.bit_length()+7)//8, 'little')
        require(hashlib.sha256(raw).hexdigest() == binding['payloads'][key]['sha256'],
                'authentic native port '+key)
    tile = json.loads((ROOT/'coefficients/wang943_tiles.json').read_text())[0]
    c0 = 1 + sum(1 << (10+2*(10*t+j)) for t, lab in enumerate(tile)
                 for j in range(10) if ((lab+512)>>j)&1)
    c0 += sum(1 << (10+2*j) for j in range(40,44))
    require(c0 == 105534389824824194647382298625, 'leading Start coefficient')
    final = {'beta':ports['beta'], 'K0':ports['K'], 'MC':ports['MC'],
             'MF':ports['MF_source'], 'cone_A':1 << 1113,
             'cone_B':1 << 666104}
    require(final['cone_A'] >= 2 and final['cone_B'] >= 2,
            'sign-recovery scale bounds')
    require((1 << 96) <= c0 and c0+1 <= 3*(1 << 95),
            'canonical leading coefficient interval')
    require(121*8791+1113 == 1064921-97 and
            121*3296+666104 == 1064921-1, 'power-of-two scale alignment')
    payload = ROOT/'coefficients/payloads'
    payload.mkdir(exist_ok=True)
    records = {}
    for name, value in final.items():
        raw = value.to_bytes((value.bit_length()+7)//8,'little')
        packed = gzip.compress(raw, mtime=0)
        (payload/(name+'.bin.gz')).write_bytes(packed)
        records[name] = {'path':'payloads/'+name+'.bin.gz',
                         'format':'gzip of minimal unsigned little-endian bytes',
                         'bits':value.bit_length(), 'raw_bytes':len(raw),
                         'raw_sha256':hashlib.sha256(raw).hexdigest(),
                         'gzip_bytes':len(packed),
                         'gzip_sha256':hashlib.sha256(packed).hexdigest()}
    out = {'status':'PASS', 'base_tuple':'mixed-parity-unrounded-1064921',
           'source_commit':'9cca523d9f27ad39d52993f4065cbd7e58f8bdd4',
           'c0':str(c0),
           'scales':{'cone_A':'2^1113','cone_B':'2^666104'},
           'guard':'cone_A*F*cone_B*C-(q-cone_A*F-cone_B*C)^2',
           'MF_convention':'already shifted; do not shift again',
           'payloads':records, 'raw_bytes':sum(x['raw_bytes'] for x in records.values()),
           'native_finite_audit':audit,
           'scope':'exact finite coefficient construction; no search for a refutation'}
    (ROOT/'coefficients/NEW_BINDING.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS','raw_bytes':out['raw_bytes'],
                     'new_guard_scales_bits':{k:records[k]['bits'] for k in ('cone_A','cone_B')},
                     'native_basis_checks':audit['basis_convolution_checks']},indent=2))


if __name__ == '__main__':
    main()
