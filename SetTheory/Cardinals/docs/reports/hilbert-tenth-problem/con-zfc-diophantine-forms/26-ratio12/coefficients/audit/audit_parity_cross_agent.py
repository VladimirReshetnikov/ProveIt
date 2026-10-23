#!/usr/bin/env python3
"""Independent literal reconstruction of the parity943 coefficient tuple.

Imports no coefficient builder, materializer, or existing geometry auditor.
The only inherited input is the pinned inert ordered tile list.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import gzip
import json

HERE = Path(__file__).resolve().parent
BASE = HERE.parent/'compiler'


def require(condition, label):
    if not condition:
        raise ValueError(label)


def main():
    tile_bytes = (BASE/'wang943_tiles.json').read_bytes()
    require(sha256(tile_bytes).hexdigest() ==
            '66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f',
            'pinned tile hash')
    tiles = json.loads(tile_bytes)
    require(len(tiles) == 943 and len(set(map(tuple, tiles))) == 943, 'tile count')
    radix_bits, cell_length = 625, 15625
    d = radix_bits*cell_length
    a, rho = 1024, 1 << radix_bits
    copy = [[base+2*j for j in range(10)] for base in (1020,1000,980,960)]
    anchors, dummies = (1095,1096,2195,3296), (1063,1064)
    support = set(range(943)) | set(sum(copy, [])) | set(anchors) | set(dummies)
    require(len(support) == 989, 'support count')
    coefficients = {}
    for idx, tile in enumerate(tiles):
        value = 1 + sum(a**j for j in range(41,45))
        for slot, label in enumerate(tile):
            require(0 <= label < 512, 'label range')
            for bit in range(10):
                value += (((label+512) >> bit) & 1) * a**(1+10*slot+bit)
        coefficients[idx] = value
    for slot in range(4):
        for bit in range(10):
            coefficients[copy[slot][bit]] = a**(1+10*slot+bit)
    coefficients.update({position:a**(41+j) for j,position in enumerate(anchors)})
    coefficients.update({position:0 for position in dummies})
    mu = a-2 + sum((a-3)*a**j for j in range(1,45)) + ((1<<78)-1)*(1<<450)
    require(mu.bit_count() == 483, 'mu population')
    coeff_sum = sum(coefficients.values())
    require(coeff_sum < a**45, 'no inner-radix overflow')
    require(max((coeff_sum//a**j)%a for j in range(45)) == 944, 'inner digits')
    dc = Counter({40:1,41:1,1100:1,2200:1})
    for e, c in coefficients.items():
        if c:
            dc[7631-e] += c
            dc[8733-e] += c
    require(max(dc.values()) < rho, 'DC digit size')
    tests = []
    for j in range(10):
        tests.append((1000+2*j,960+2*j,None,1000+2*j))
        tests.append((1021+2*j,980+2*j,1020+2*j,None))
    tests += [(2195,1095,None,2195),(3296,1096,None,3296)]
    basis_checks = 0
    for target,current,spatial,temporal in tests:
        for e in support:
            require(dc.get(target-e,0) == int(e == current), 'DC target isolation')
            require(int(e+1 == target) == int(e == spatial), 'DR target isolation')
            require(int(e == target) == int(e == temporal), 'temporal target isolation')
            basis_checks += 3
    for target in (7631,8733):
        for e in support:
            require(dc.get(target-e,0) == coefficients[e], 'clause target')
            require(e+1 != target, 'clause DR isolation')
            basis_checks += 2
    require(1064 in support, 'upper dummy spill included')
    require(not ({(7631-e)%cell_length for e in support} &
                 {(8733-e)%cell_length for e in support}), 'all-rotation clean bands')
    require({(2195-e)%cell_length for e in support} &
            {(3296-e)%cell_length for e in support} == {0}, 'unique anchor alignment')
    require(min(dc) > 0 and max(dc)+max(support) < cell_length, 'DC positive and no cell spill')
    require(1+max(support) < cell_length, 'DR no cell spill')
    mass = (len(support)+2)*(2*coeff_sum+6)
    threshold = max(4*mass+8,2*mu+4,16)
    require(threshold < rho, 'uniform carry threshold')
    require(3*rho//4+mass <= rho-2 and rho//2+1+mass <= rho-2, 'strict slack')
    unit = (2*sum(c*pow(2,e,5) for e,c in dc.items())-2)%5
    require(unit == 3, 'five-adic unit')
    require(pow(2,1063,5)*3*unit%5 == 2, 'dummy derivative')

    cleared = {radix_bits*e for e in support if e != 1} | {radix_bits*1063+1}
    field = {2} | {radix_bits*t for t,_,_,_ in tests}
    for band in (7631,8733):
        field |= {radix_bits*band+bit for bit in range(mu.bit_length()) if mu>>bit&1}
    require(len(cleared) == len(field) == 989, 'balanced masks')
    beta = (1<<d)-1
    mc = beta-sum(1<<bit for bit in cleared)
    mf_native = sum(1<<bit for bit in field)
    mf_source = mf_native+beta
    require(mc%4 == 2 and mf_native%8 == 4, 'low mask congruences')
    require(mc.bit_count()+mf_native.bit_count() == d, 'mask population sum')
    # Construct K by disjoint base-rho fields rather than repeated giant sums.
    k_bytes = bytearray((d+radix_bits+1+7)//8)
    def put(value, bit_position):
        start, shift = divmod(bit_position,8)
        value <<= shift
        encoded = value.to_bytes((value.bit_length()+7)//8,'little')
        for j, byte in enumerate(encoded):
            require(k_bytes[start+j]&byte == 0, 'K overlapping binary fields')
            k_bytes[start+j] |= byte
    for e,c in dc.items():
        put(c,radix_bits*e)
    put(1,d+radix_bits)
    expected = {
        'beta': beta.to_bytes((beta.bit_length()+7)//8,'little'),
        'MC': mc.to_bytes((mc.bit_length()+7)//8,'little'),
        'MF_source': mf_source.to_bytes((mf_source.bit_length()+7)//8,'little'),
        'K': bytes(k_bytes),
    }
    files = {}
    for name, wanted in expected.items():
        raw_path = BASE/'coefficients_parity'/f'{name}.bin'
        compressed = (BASE/'coefficients_parity'/f'{name}.bin.gz').read_bytes()
        actual = raw_path.read_bytes() if raw_path.exists() else gzip.decompress(compressed)
        require(actual == wanted, 'exact coefficient bytes '+name)
        require(gzip.decompress(compressed) == wanted, 'gzip coefficient '+name)
        value = int.from_bytes(actual,'little')
        files[name] = {'bytes':len(actual),'bits':value.bit_length(),
                       'sha256':sha256(actual).hexdigest(),'gzip_bytes':len(compressed)}
    receipt = {
        'status':'PASS', 'basis_convolution_checks':basis_checks,
        'native_support_count':989, 'field_mask_population':989,
        'data_mask_population':d-989, 'five_adic_unit':unit,
        'dummy_derivative_mod5':2, 'mass_bits':mass.bit_length(),
        'threshold_bits':threshold.bit_length(),
        'max_unshifted_exponent':max(dc)+max(support),
        'all_rotation_clean_bands':True,'anchor_alignment_intersection':[0],
        'positive_DC_DR_degree':True,'strict_slack_bounds':True,
        'files':files,'total_bytes':sum(x['bytes'] for x in files.values()),
        'total_gzip_bytes':sum(x['gzip_bytes'] for x in files.values()),
        'scope':'Independent exact literal tuple reconstruction and finite geometry. Universal synchronization/adapter reasoning is in the companion review; the inherited compiler and K215 calibration remain dependencies.'
    }
    (HERE/'PARITY_CROSS_AGENT_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__ == '__main__':
    main()
