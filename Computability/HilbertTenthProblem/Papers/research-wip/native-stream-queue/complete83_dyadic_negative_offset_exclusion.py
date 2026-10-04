"""Fresh bounded arithmetic evidence; every predecessor is read as inert data.

This is a conditional valid-compiler theorem supplement, not an emitted new
compiler, native-zero search, or execution of any inherited DAG/helper.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import comb
from pathlib import Path

PINS = {
    'complete83_shared_projection_scout.json': 'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
    'complete83_shared_projection_scout.md': 'e36f465f257836c972b0edf10b865580e14427360d37799433fa7f301a85a4b8',
    'complete83_shared_projection_math.md': '1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c',
    'review_complete83_shared_projection_math.md': '8ed2a92dfdc4a8a4c799cdef86adda5af467050704eaefc451eea14ffbed80bb',
    'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
    'pell_kernel_half_binomial42.md': '0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992',
    '../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md': '75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87',
    '../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md': 'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39',
}
ROWS = [
    ['repunit', '*', 'Bm1', 'Jrep'], ['q', '+', 'repunit', 1],
    ['Lbig', '*', 'q', 'q'], ['n2', '*', 'Lbig', 'q'],
    ['wn2', '*', 'w', 'q'], ['sn2', '*', 's', 'n2'],
    ['UM', '*', 'wn2', 'sn2'], ['R10b', '+', 'eta', 'zeta'],
    ['ksn2', '*', 'R10b', 'sn2'], ['R10a', '+', 'ksn2', 'eta'],
    ['R12', '+', 'UM', 'sn2'], ['D1', '+', 'wn2', 'cam2'],
    ['a4m5', '+', 'a4', 3], ['gam', '*', 'sigma', 'a4m5'],
    ['shared_main_partial', '+', 'D1', 'shared_projection'],
    ['R14', '+', 'shared_main_partial', 'gam'],
    ['q_minus_F', '-', 'q', 'F'], ['q_minus_FZ', '-', 'q_minus_F', 'Z'],
    ['C_after_alpha', '-', 'q_minus_FZ', 'alpha'],
    ['scaled_t', '*', 'twice_cell_bits', 'x'],
    ['marked_rhs', '-', 'C_after_alpha', 'scaled_t'],
    ['W', '-', 'marked_rhs', 'Z'],
    ['odd_index', '+', 'scaled_t', 'inner_bits'],
    ['exponent_rhs', '+', 'exponent_partial', 'shared_projection'],
    ['gap_product', '*', 'repunit', 'q_minus_F'],
    ['gap', '+', 'gap_product', 'q_minus_FZ'],
    ['Lm1', '-', 'Lbig', 1], ['rproduct', '*', 'gap', 'Lm1'],
    ['qMF', '*', 'q', 'MF'], ['mask_factor', '+', 'MC', 'qMF'],
    ['mask', '*', 'mask_factor', 'Jrep'], ['r_lhs', '+', 'rproduct', 'mask'],
]

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def unique(pairs):
    d = {}
    for k, v in pairs:
        require(k not in d, 'duplicate JSON key')
        d[k] = v
    return d

def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique)

def v2(n):
    require(n != 0, 'zero valuation')
    n = abs(n)
    return (n & -n).bit_length() - 1

def row_guards(root):
    for name, digest in PINS.items():
        require(sha((root / name).read_bytes()) == digest, 'pin ' + name)
    p = read_json(root / 'complete83_shared_projection_scout.json')['packet']
    rows = p['source']
    d = {r[0]: r for r in rows}
    require(len(d) == len(rows) == 83, 'source uniqueness/count')
    for row in ROWS:
        require(d.get(row[0]) == row, 'literal interface ' + row[0])
    require(Counter(r[1] for r in rows) == Counter({'*':46, '+':20, '-':17}), 'ledger')
    require(len(p['witnesses']) == 18 and p['ordinary_input'] == 'x', 'domain')
    require(p['fixed_numerals'] == ['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF'], 'numerals')
    return {'literal_interface_rows': len(ROWS), 'total_source_rows_read': len(rows),
            'ledger': {'M':46,'A':37}, 'positive_witnesses':18,
            'prior_source_evaluated':False}

def arithmetic():
    modular_cases = 0
    dig = hashlib.sha256()
    # Exact full half-binomial modular sums versus the four-term reduction.
    # These are small scalar examples, not valid-program zeros.
    for r in range(25, 256, 2):
        coeffs = [comb(2*r, r)]
        for j in range(r):
            numerator = coeffs[-1] * (r-j)
            require(numerator % (r+j+1) == 0, 'binomial recurrence')
            coeffs.append(numerator // (r+j+1))
        require(coeffs[-1] == 1, 'last coefficient')
        for t in range(4, 11):
            modulus = 1 << (3*t+1)
            for ell in sorted({t,t+1,2*t,3*t+1}):
                R = 2*r+1
                require(R > 3*t+1 and ell < R, 'example exponent domain')
                X = (1 << R) - (1 << ell)
                full = 0
                for c in reversed(coeffs):
                    full = (full*X+c) % modulus
                short = sum(coeffs[j] * (-(1 << ell))**j for j in range(4)) % modulus
                require(full == short, 'four-term reduction')
                require(full % 2 == 0, 'half-integrality')
                require((full == 0) == ((full//2) % (1 << (3*t)) == 0), 'cubed scale')
                dig.update(f'{r},{t},{ell},{full}\n'.encode())
                modular_cases += 1
    valuation_cases = 0
    for r in range(25, 4096, 2):
        p, k, ell3, h = r.bit_count(), v2(r+1), v2(r+3), v2(r-1)
        cs = [comb(2*r, r+j) for j in range(4)]
        expected = [p,p-k,p+h-k,p+h-k-ell3]
        require([v2(c) for c in cs] == expected, 'coefficient valuations')
        for t in range(4, 13):
            if k > t-2 or ell3 > t-2:
                continue
            weighted = [v2(cs[j])+j*t for j in range(4)]
            require(all(v > p for v in weighted[1:]), 'unique central valuation')
            cubic = sum(cs[j] * (-(1 << t))**j for j in range(4))
            require(v2(cubic) == p, 'cubic valuation')
            require((cubic % (1 << (3*t+1)) == 0) == (p >= 3*t+1), 'threshold')
            valuation_cases += 1
    # Check the residue contradiction independently of any manufactured program.
    residue_cases = 0
    for t in range(4, 9):
        q = 1 << t
        for Drep in range(4, q):
            for Z in range(Drep+1, q):
                Rlow = (Z-Drep-1) % q
                require(Rlow not in (q-1,q-5), 'forbidden low residues')
                residue_cases += 1
    # This deliberately violates the l<=t-2 guard: k<t alone is insufficient.
    t, r = 4, (1 << 13)-3
    cs = [comb(2*r, r+j) for j in range(4)]
    weighted = [v2(cs[j])+j*t for j in range(4)]
    cubic = sum(cs[j] * (-(1 << t))**j for j in range(4))
    require(weighted == [12,15,21,12], 'exception weights')
    require(v2(cubic) > 12, 'exception cancellation')
    return {'full_half_binomial_modular_cases':modular_cases,
            'modular_records_sha256':dig.hexdigest(),
            'guarded_cubic_valuation_cases':valuation_cases,
            'negative_branch_residue_cases':residue_cases,
            'unrestricted_k_only_counterexample':{'t':t,'r':r,'central_valuation':12,
                 'k':v2(r+1),'l':v2(r+3),'weighted_valuations':weighted,
                 'cubic_valuation':v2(cubic), 'valid_compiler_zero_claimed':False},
            'native_or_Pell_zeros_materialized':False}

def build(root):
    interface = row_guards(root)
    return {'source_sha256':sha(Path(__file__).read_bytes()), 'pins':PINS,
            'scope':{'conditional_q_dyadic':True,'valid_compiler_required':True,
                     'excludes':'u<t and W=2^u-q',
                     'still_open':['q non-dyadic','u>=t, W=0'],
                     'new_universal_operation_bound':False},
            'source_interface':interface, 'finite_evidence':arithmetic()}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--output', type=Path)
    group.add_argument('--expect', type=Path)
    a = ap.parse_args()
    result = build(a.root)
    encoded = json.dumps(result, sort_keys=True, indent=2) + '\n'
    if a.output:
        with a.output.open('x') as f:
            f.write(encoded)
    else:
        require(a.expect.read_text() == encoded, 'exact receipt replay')
    print('PASS: dyadic negative-offset exclusion evidence; no native-zero claim')

if __name__ == '__main__':
    main()
