#!/usr/bin/env python3
"""Exact residues of the four fixed, pruned-T4 K215 coefficients.

Place this file beside PRUNED_T4_CONSTANTS.json and pruned_t4_windows.json.
Only modular arithmetic is used; no enormous coefficient is expanded.

API: coefficient_residues(modulus, data_dir=None) -> dict with the ports
Bm1, Kconstant, MC, MF. Every call authenticates the exact recipe and tiles.
CLI: python3 coefficient_residues.py --modulus 1000000007
Audit: python3 coefficient_residues.py --verify --receipt residue_checks.json

All validation remains active under python -O. Standard library only.
"""
from pathlib import Path
import argparse
import hashlib
import json
import tempfile

RECIPE_FILE = 'PRUNED_T4_CONSTANTS.json'
RECIPE_SHA256 = '9a314993a5ca523dc5f56d9e175540fc990341f39d0862b3aed4c29612dc853e'
TILES_FILE = 'pruned_t4_windows.json'
TILES_SHA256 = 'baa3d2b5296b818b2e6488c1b06fda29e405d9b4cf5dd19a3c38fbdd1ba658d7'
BINDING = 'pruned-T4-5252-compact-5pow16'
ELL, RADIX_EXP, CELL_LENGTH = 13, 78125, 1953125
BINARY_EXP = 152587890625
EMAX, T1, T2, HC = 82873, 771293, 937043, 605107
COPY_OFFSETS = (8764, 8325, 7886, 7008)
COPY_POWERS = (1, 440, 879, 1318)
ANCHORS = (11839, 23678, 35517, 82873)
DUMMIES = (10520, 10521)
PORTS = ('Bm1', 'Kconstant', 'MC', 'MF')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def _modulus(modulus):
    require(type(modulus) is int and modulus > 0, 'modulus must be a positive integer')
    return modulus


def _authenticated_data(data_dir=None):
    root = Path(data_dir) if data_dir is not None else Path(__file__).resolve().parent
    raw_recipe = (root / RECIPE_FILE).read_bytes()
    require(hashlib.sha256(raw_recipe).hexdigest() == RECIPE_SHA256,
            'coefficient recipe SHA-256 mismatch')
    recipe = json.loads(raw_recipe)
    require(recipe['binding'] == BINDING, 'coefficient binding mismatch')
    require(recipe['tiles']['file'] == TILES_FILE and
            recipe['tiles']['sha256'] == TILES_SHA256, 'tile binding mismatch')
    raw_tiles = (root / TILES_FILE).read_bytes()
    require(hashlib.sha256(raw_tiles).hexdigest() == TILES_SHA256,
            'ordered tile list SHA-256 mismatch')
    tiles = json.loads(raw_tiles)
    require(len(tiles) == 5252, 'wrong tile count')
    require(all(type(row) is list and len(row) == 4 and
                all(type(x) is int and 0 <= x < 439 for x in row) for row in tiles),
            'malformed tile')
    require(tiles[:2] == [[434, 435, 436, 1], [438, 0, 0, 438]],
            'wrong distinguished tile order')
    require(len(set(map(tuple, tiles))) == len(tiles), 'duplicate tile')
    require(tiles[2:] == sorted(tiles[2:]), 'wrong remaining tile order')
    scalars = recipe['scalars']
    for name, expected in [('ell', ELL), ('b', RADIX_EXP), ('L', CELL_LENGTH),
                           ('d', BINARY_EXP), ('Emax', EMAX), ('T1', T1),
                           ('T2', T2), ('Hc', HC), ('native_support', 7014)]:
        require(scalars[name] == expected, 'wrong fixed scalar: ' + name)
    require(RADIX_EXP * CELL_LENGTH == BINARY_EXP, 'inconsistent fixed exponent')
    return recipe, tiles


def _power_sum(base, count, modulus):
    """Return (base**count, sum(base**j, 0<=j<count)) modulo modulus.

    Concatenating lengths r and s uses S_(r+s)=S_r+base^r*S_s.
    This uses no division and is valid for nonunits and composite moduli.
    """
    require(type(count) is int and count >= 0, 'negative geometric-sum length')
    power, total = 1 % modulus, 0
    block_power, block_total = base % modulus, 1 % modulus
    while count:
        if count & 1:
            total = (total + power * block_total) % modulus
            power = power * block_power % modulus
        block_total = (block_total + block_power * block_total) % modulus
        block_power = block_power * block_power % modulus
        count >>= 1
    return power, total


def _sparse_horner(terms, base, modulus):
    """Evaluate an integer polynomial supplied as exponent:coefficient."""
    result, previous = 0, max(terms, default=0)
    cache = {0: 1 % modulus, 1: base % modulus}
    for exponent in sorted(terms, reverse=True):
        gap = previous - exponent
        if gap not in cache:
            cache[gap] = pow(base, gap, modulus)
        result = (result * cache[gap] + terms[exponent]) % modulus
        previous = exponent
    return result * pow(base, previous, modulus) % modulus


def _weights(tiles, modulus):
    a0 = pow(2, ELL, modulus)
    ap = [1 % modulus]
    for _ in range(2835):
        ap.append(ap[-1] * a0 % modulus)
    anchor_part = sum(ap[1757:1761]) % modulus
    weights = {}

    def insert(position, value):
        require(position not in weights, 'overlapping fixed support')
        weights[position] = value % modulus

    for index, tile in enumerate(tiles):
        insert(index, 1 + anchor_part + sum(ap[shift + symbol]
               for shift, symbol in zip(COPY_POWERS, tile)))
    for offset, shift in zip(COPY_OFFSETS, COPY_POWERS):
        for symbol in range(439):
            insert(offset + symbol, ap[shift + symbol])
    for index, position in enumerate(ANCHORS):
        insert(position, ap[1757 + index])
    for position in DUMMIES:
        insert(position, 0)
    require(len(weights) == 7014 and max(weights) == EMAX, 'wrong fixed support')
    mu = (a0 - 2 + sum(ap[1:])) % modulus
    return weights, mu


def _compute(tiles, modulus):
    """Fast exact evaluation after authentication, including audit internals."""
    rho = pow(2, RADIX_EXP, modulus)
    base = pow(2, BINARY_EXP, modulus)
    weights, mu = _weights(tiles, modulus)
    cache = {}

    def rp(exponent):
        if exponent not in cache:
            cache[exponent] = pow(rho, exponent, modulus)
        return cache[exponent]

    # H(rho)=sum(v_e*rho**(Emax-e)); the two clause bands share H.
    reverse_polynomial = _sparse_horner(
        {EMAX - position: value for position, value in weights.items()}, rho, modulus)
    dc = (sum(rp(j) for j in (1317, 605546, 23678, 59195)) +
          (rp(T1 - EMAX) + rp(T2 - EMAX)) * reverse_polynomial) % modulus
    dr = rp(HC)
    _, symbols_sum = _power_sum(rho, 439, modulus)
    _, selectors_sum = _power_sum(rho, 5252, modulus)
    support_except_one = (selectors_sum - rho +
        symbols_sum * sum(rp(offset) for offset in COPY_OFFSETS) +
        sum(rp(position) for position in DUMMIES + ANCHORS)) % modulus
    mf_native = (mu * (rp(T1) + rp(T2)) +
        symbols_sum * sum(rp(offset) for offset in (8325, 613871, 613432)) +
        rp(35517) + rp(82873) + 4) % modulus
    return {'Bm1': (base - 1) % modulus,
            'Kconstant': (dc + base * dr) % modulus,
            'MC': (base - 1 - support_except_one - 2 * rp(10520)) % modulus,
            'MF': (mf_native + base - 1) % modulus,
            'DC': dc, 'DR': dr, 'MF_native': mf_native}


def coefficient_residues(modulus, data_dir=None):
    """Return Bm1,Kconstant,MC,MF modulo any positive integer modulus.

    MF is the shifted source port, not the native mask. The exact recipe
    and ordered tile bytes are authenticated on each call.
    """
    modulus = _modulus(modulus)
    _, tiles = _authenticated_data(data_dir)
    values = _compute(tiles, modulus)
    return {name: values[name] for name in PORTS}


def _literal_reference(tiles, modulus):
    """Independent literal finite-sum implementation using powers of 2.

    No sparse Horner, grouped bands, geometric sum, or _weights call is
    shared with the production assembly.
    """
    def ap(exponent): return pow(2, 13 * exponent, modulus)
    def rp(exponent): return pow(2, 78125 * exponent, modulus)
    coefficients = {}
    for index, (left, center, right, nxt) in enumerate(tiles):
        coefficients[index] = (1 + ap(1+left) + ap(440+center) + ap(879+right) +
                              ap(1318+nxt) + sum(ap(1756+j) for j in range(1,5))) % modulus
    for u in range(439):
        coefficients[8764+u] = ap(1+u)
        coefficients[8325+u] = ap(440+u)
        coefficients[7886+u] = ap(879+u)
        coefficients[7008+u] = ap(1318+u)
    for j, position in enumerate((11839,23678,35517,82873), 1):
        coefficients[position] = ap(1756+j)
    coefficients[10520] = coefficients[10521] = 0
    dc = (rp(1317)+rp(605546)+rp(23678)+rp(59195)+
          sum(value*(rp(771293-position)+rp(937043-position))
              for position,value in coefficients.items())) % modulus
    dr = rp(605107)
    base = pow(2, 152587890625, modulus)
    mu = (ap(1)-2+sum(ap(j) for j in range(1,2836))) % modulus
    mf_native = (mu*(rp(771293)+rp(937043))+
        sum(rp(8325+u)+rp(613871+u)+rp(613432+u) for u in range(439))+
        rp(35517)+rp(82873)+4) % modulus
    return {'Bm1':(base-1)%modulus, 'Kconstant':(dc+base*dr)%modulus,
            'MC':(base-1-sum(rp(j) for j in coefficients if j != 1)-2*rp(10520))%modulus,
            'MF':(mf_native+base-1)%modulus, 'DC':dc, 'DR':dr,
            'MF_native':mf_native}


def verify(data_dir=None):
    """Finite implementation audit; not a proof of compiler semantics."""
    recipe, tiles = _authenticated_data(data_dir)
    moduli = [1,2,4,5,8,9,16,97,256,65521,1000000007,4294967296]
    rows = []
    for modulus in moduli:
        fast, literal = _compute(tiles, modulus), _literal_reference(tiles, modulus)
        require(fast == literal, 'literal-reference mismatch modulo '+str(modulus))
        rows.append({'modulus':modulus, **{name:fast[name] for name in PORTS}})
    mod8 = _compute(tiles,8)
    require(mod8['MC']%4 == 2 and mod8['MF_native'] == 4 and mod8['MF'] == 3,
            'low mask congruence failed')
    mod5 = _compute(tiles,5)
    require(mod5['DC'] == 3 and mod5['DR'] == 3 and
            (2*mod5['DC']-mod5['DR'])%5 == 3 and mod5['Kconstant'] == 4,
            'five-adic tuning congruence failed')
    miniature_cases = 0
    for modulus in (1,4,6,9,17):
        for base in (0,1,2,3,6):
            for count in (0,1,2,3,7,13):
                actual = _power_sum(base,count,modulus)
                expected = (pow(base,count,modulus),sum(base**j for j in range(count))%modulus)
                require(actual == expected, 'geometric-sum miniature mismatch')
                miniature_cases += 1
    for bad in (0,-1,True,1.5):
        try: coefficient_residues(bad,data_dir)
        except ValueError: pass
        else: raise ValueError('invalid modulus accepted')
    source = Path(data_dir) if data_dir is not None else Path(__file__).resolve().parent
    tamper_rejections = []
    with tempfile.TemporaryDirectory(prefix='proveit-residue-audit-') as directory:
        target=Path(directory)
        for name in (RECIPE_FILE,TILES_FILE):
            (target/name).write_bytes((source/name).read_bytes())
        for name in (RECIPE_FILE,TILES_FILE):
            original=(target/name).read_bytes()
            (target/name).write_bytes(original+b' ')
            try: coefficient_residues(97,target)
            except ValueError: tamper_rejections.append(name)
            else: raise ValueError('tampered data accepted: '+name)
            (target/name).write_bytes(original)
    return {'schema':'proveit-fixed-coefficient-residue-verification-v1',
            'binding':recipe['binding'], 'recipe_sha256':RECIPE_SHA256,
            'tiles_sha256':TILES_SHA256, 'tile_count':len(tiles),
            'support_count':7014, 'literal_comparison_moduli':moduli,
            'literal_comparison_internal_values':7*len(moduli),
            'low_congruences':{'MC_mod4':2,'MF_native_mod8':4,'MF_source_mod8':3,
                'DC_mod5':3,'DR_mod5':3,'2DC_minus_DR_mod5':3,'Kconstant_mod5':4},
            'geometric_sum_miniature_cases':miniature_cases,
            'tamper_rejections':tamper_rejections,
            'invalid_moduli_rejected':4, 'residues':rows,
            'scope':'Exact arithmetic implementation audit; no coefficient expansion, accepting computation, or compiler-semantic proof.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--modulus',type=int)
    parser.add_argument('--data-dir',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--verify',action='store_true')
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args()
    if args.modulus is None and not args.verify:
        parser.error('provide --modulus N or --verify')
    if args.receipt is not None and not args.verify:
        parser.error('--receipt requires --verify')
    try:
        if args.verify:
            result=verify(args.data_dir)
            if args.receipt:
                args.receipt.write_text(json.dumps(result,indent=2)+'\n')
            print(json.dumps(result,indent=2))
        if args.modulus is not None:
            result={'modulus':_modulus(args.modulus),
                    **coefficient_residues(args.modulus,args.data_dir),
                    'binding':BINDING, 'recipe_sha256':RECIPE_SHA256,
                    'tiles_sha256':TILES_SHA256,
                    'method':'Authenticated exact finite sums, modular powers and division-free Horner evaluation'}
            print(json.dumps(result,indent=2))
    except (ValueError,OSError) as error:
        parser.exit(2,str(error)+'\n')


if __name__=='__main__':
    main()
