#!/usr/bin/env python3
"""Deterministic literal U209 -> U208 edit, with a checked dense renaming."""
import argparse, hashlib, json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_PARENT = 'd0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16'
EXPECTED_NATIVE = '527c2a6065ba7c9adb09294eed2b532810d812e46df4b5b912bae99ae6fb3a3a'
EXPECTED_DENSE = '9f4ea95849c5e1d01fa3f740023092230cd7006eed650b94a2d5da537e25212c'

def need(ok, message):
    if not ok: raise ValueError(message)

def encode(table):
    return ('#! start 0\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {t}\n'
        for (q,b),(w,d,t) in sorted(table.items()))).encode('ascii')

def build(output):
    output = Path(output); output.mkdir(parents=True, exist_ok=True)
    raw = (ROOT/'baseline/u209.native.tm').read_bytes()
    need(hashlib.sha256(raw).hexdigest() == EXPECTED_PARENT, 'Parent hash')
    old = {}
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#') or not line: continue
        q,b,w,d,t = line.split()
        key = int(q),int(b)
        need(key not in old, 'Duplicate transition')
        old[key] = int(w), 1 if d == 'R' else -1, int(t)
    need(len(old) == 418, 'Parent row count')
    rho = lambda q: 172 if q == 211 else q
    new = {(q,b):(w,d,rho(t)) for (q,b),(w,d,t) in old.items() if q != 211}
    new[172,0] = 0,-1,217
    states = sorted({q for q,b in new})
    need(len(states) == 208 and set(new) == {(q,b) for q in states for b in (0,1)}, 'Complete 208-state table')
    rename = {q:i for i,q in enumerate(states)}; rename[254] = 208
    inverse = {v:k for k,v in rename.items()}
    dense = {(rename[q],b):(w,d,rename[t]) for (q,b),(w,d,t) in new.items()}
    need({(inverse[q],b):(w,d,inverse[t]) for (q,b),(w,d,t) in dense.items()} == new, 'Dense conjugacy')
    native_raw, dense_raw = encode(new), encode(dense)
    need(hashlib.sha256(native_raw).hexdigest() == EXPECTED_NATIVE, 'Native output hash')
    need(hashlib.sha256(dense_raw).hexdigest() == EXPECTED_DENSE, 'Dense output hash')
    (output/'u208.native.tm').write_bytes(native_raw)
    (output/'u208.tm').write_bytes(dense_raw)
    (output/'state_map.json').write_text(json.dumps({'native_to_dense':rename,
        'dense_to_native':inverse,'native_halt':254,'dense_halt':208},indent=2)+'\n')
    result = {'status':'DETERMINISTIC_CONSTRUCTION_PASS','working_states':208,'rows':416,
        'start':0,'dense_halt':208,'native_halt':254,'deleted_native_state':211,
        'redirected_rows':[[163,0,0,'L',172],[163,1,1,'R',172]],
        'other_changed_row':[172,0,0,'L',217],
        'parent_sha256':EXPECTED_PARENT,'native_sha256':EXPECTED_NATIVE,'dense_sha256':EXPECTED_DENSE}
    (output/'construction.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__ == '__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    print(json.dumps(build(p.parse_args().output),indent=2))
