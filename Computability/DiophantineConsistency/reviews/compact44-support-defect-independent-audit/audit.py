#!/usr/bin/env python3
"""Exact finite support/defect reconstruction; no Lean/model claim."""
import ast
import gzip
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parents[2]
RECIPE = BASE / 'candidates/free-j-polarized-positive/source/positive/coefficients/recipe'
COEFFICIENTS = BASE / 'candidates/ten-positive-shifted-strong/coefficients'
TABLE = BASE / 'con-zfc-diophantine-forms/36-small-tuple/coefficients/wang943_tiles.json'
PINS = {
    RECIPE / 'build_coefficients.py': 'a003f26c5ef2dc1782e37be2a91abe25e59e5ff39f12bd142f2d6c1d4d8cf82b',
    RECIPE / 'COEFFICIENT_BINDING.json': '0599543212b8d2bbed2db018a29d6826702e1877faa5c8a1861d041998cb1783',
    TABLE: '66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f',
    COEFFICIENTS / 'MC.bin.gz': '271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e',
    COEFFICIENTS / 'beta.bin.gz': '466796f146d60db9929fa0f0f62d70d5e6afbcea9940342764571f1ca6bea87c',
}

def need(condition, message):
    if not condition:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def rep(w, n):
    return ((1 << (w*n))-1) // ((1 << w)-1)

def main():
    data = {p: p.read_bytes() for p in PINS}
    for p, expected in PINS.items():
        need(digest(data[p]) == expected, 'input pin: ' + str(p))
    source = data[RECIPE / 'build_coefficients.py'].decode()
    values = {}
    for node in ast.parse(source).body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id in ('WIDTHS', 'OFFSETS', 'ANCHORS'):
                    need(target.id not in values, 'duplicate builder constant')
                    values[target.id] = ast.literal_eval(node.value)
    need(values == {'WIDTHS': (9,10,9,10), 'OFFSETS': (1023,1013,1003,983),
                    'ANCHORS': (1095,2195,3296)}, 'builder constants')
    binding = json.loads(data[RECIPE / 'COEFFICIENT_BINDING.json'])
    rows = json.loads(data[TABLE])
    need(len(rows) == 943 and rows[1] == [5,0,0,0], 'selector rows')
    need(binding['L'] == 8807 and binding['b'] == 67 and binding['d'] == 590069, 'radix')
    need(binding['port_widths'] == list(values['WIDTHS']) and binding['anchors'] == list(values['ANCHORS']), 'binding constants')
    slots = [None] * 41
    positions = binding['binary_positions']
    need(len(positions) == 4, 'field count')
    for field, bits in enumerate(positions):
        need(len(bits) == values['WIDTHS'][field], 'field width')
        for j, bit in enumerate(bits):
            need(type(bit) is int and 0 <= bit < 41 and slots[bit] is None, 'field bit')
            slots[bit] = values['OFFSETS'][field]+j
    need(len(binding['anchor_positions']) == 3, 'anchor count')
    for bit, pos in zip(binding['anchor_positions'], values['ANCHORS']):
        need(type(bit) is int and 0 <= bit < 41 and slots[bit] is None, 'anchor bit')
        slots[bit] = pos
    need(None not in slots and len(set(slots)) == 41, 'copy slots')
    selectors = set(range(943)); copies = set(slots); dummies = {1063,1064}
    need(not (selectors & copies or selectors & dummies or copies & dummies), 'overlap')
    support = selectors | copies | dummies
    concise = set(range(943)) | set(range(983,993)) | set(range(1003,1012)) | set(range(1013,1032)) | {1063,1064,1095,2195,3296}
    need(support == concise and len(support) == 986, 'support intervals')
    support_word = sum(1 << e for e in support)
    support_closed = (rep(1,943) + (1<<983)*rep(1,10) + (1<<1003)*rep(1,9)
                      + (1<<1013)*rep(1,19) + sum(1<<e for e in (1063,1064,1095,2195,3296)))
    need(support_word == support_closed, 'support repunit identity')
    rho = 1 << 67
    power = lambda e: 1 << (67*e)
    beta = (1 << 590069)-1
    mc_raw = gzip.decompress(data[COEFFICIENTS / 'MC.bin.gz'])
    beta_raw = gzip.decompress(data[COEFFICIENTS / 'beta.bin.gz'])
    need(digest(mc_raw) == '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4', 'MC raw')
    need(digest(beta_raw) == '0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d', 'beta raw')
    mc = int.from_bytes(mc_raw, 'little')
    need(int.from_bytes(beta_raw, 'little') == beta, 'retained beta')
    D = sum(power(e) for e in support if e != 1) + 2*power(1063)
    D_closed = (1 + power(2)*rep(67,941) + power(983)*rep(67,10)
                + power(1003)*rep(67,9) + power(1013)*rep(67,19)
                + 3*power(1063) + sum(power(e) for e in (1064,1095,2195,3296)))
    need(D == D_closed and mc+D == beta, 'defect/retained MC')
    for j in range(8807):
        delta = 0 if j == 1 else 3 if j == 1063 else (support_word >> j) & 1
        need(((mc >> (67*j)) & (rho-1)) + delta == rho-1, 'digit '+str(j))
    controls = {
        'position_1_not_removed': sum(power(e) for e in support) + 2*power(1063),
        'dummy_1063_only_weight_1': sum(power(e) for e in support if e != 1),
        'dummy_1064_omitted': D-power(1064),
        'copy_slot_1013_omitted': D-power(1013),
    }
    for name, altered in controls.items():
        need(mc+altered != beta, 'mutation survived: '+name)
    for p, expected in PINS.items():
        need(digest(p.read_bytes()) == expected, 'post-check input drift: '+str(p))
    print(json.dumps({'status':'PASS_COMPACT44_SUPPORT_DEFECT_FINITE', 'support_size':len(support),
        'digits_checked':8807, 'mutations_rejected':list(controls),
        'mc_raw_sha256':digest(mc_raw), 'beta_raw_sha256':digest(beta_raw),
        'scope':'finite external arithmetic only; no all-model MC equality, graph binding, NoCarry, or iPRA proof'}, indent=2))

if __name__ == '__main__':
    main()
