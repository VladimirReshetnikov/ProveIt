"""Independent scoped checks. Read frozen proof/source bytes; execute only this file."""
import argparse
import hashlib
import json
from collections import Counter
from math import comb
from pathlib import Path

AUTHOR = {
    '.py': '1bfe8166349fbd16b8557c87cccbbe9827f0eb0813c6227858c22a1fb5a32b35',
    '.json': '6231bded06dbd82575414566cf0ddbd63594f2d21529e36a484cb024b4365144',
    '.md': '9e24c06c8627e50718f0b00236df7dbb83e8ac9701bc3536e097148b3ae922f2',
}
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
# Independent named producer guards for the exact scalar identities used below.
OUTER = {
 'repunit': ('*','Bm1','Jrep'), 'q': ('+','repunit',1),
 'Lbig': ('*','q','q'), 'n2': ('*','Lbig','q'),
 'wn2': ('*','w','q'), 'sn2': ('*','s','n2'),
 'q_minus_F': ('-','q','F'), 'q_minus_FZ': ('-','q_minus_F','Z'),
 'C_after_alpha': ('-','q_minus_FZ','alpha'),
 'scaled_t': ('*','twice_cell_bits','x'),
 'marked_rhs': ('-','C_after_alpha','scaled_t'),
 'W': ('-','marked_rhs','Z'), 'odd_index': ('+','scaled_t','inner_bits'),
 'gap_product': ('*','repunit','q_minus_F'),
 'gap': ('+','gap_product','q_minus_FZ'), 'Lm1': ('-','Lbig',1),
 'rproduct': ('*','gap','Lm1'), 'qMF': ('*','q','MF'),
 'mask_factor': ('+','MC','qMF'), 'mask': ('*','mask_factor','Jrep'),
 'r_lhs': ('+','rproduct','mask'),
}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def unique(pairs):
    d = {}
    for k, v in pairs:
        need(k not in d, 'duplicate key')
        d[k] = v
    return d

def load(path):
    return json.loads(path.read_text(), object_pairs_hook=unique)

def factorial_v2(n):
    result = 0
    while n:
        n //= 2
        result += n
    return result

def valuation(n):
    need(n != 0, 'zero valuation')
    n = abs(n)
    result = 0
    while n % 2 == 0:
        n //= 2
        result += 1
    return result

def inspect(root, author):
    for ext, digest in AUTHOR.items():
        need(sha(Path(str(author)+ext).read_bytes()) == digest, 'author pin '+ext)
    for name, digest in PINS.items():
        need(sha((root/name).read_bytes()) == digest, 'predecessor pin '+name)
    packet = load(root/'complete83_shared_projection_scout.json')['packet']
    source = packet['source']
    rows = {row[0]: tuple(row[1:]) for row in source}
    need(len(rows) == len(source) == 83, 'row uniqueness/count')
    for name, rhs in OUTER.items():
        need(rows[name] == rhs, 'outer producer '+name)
    counts = Counter(row[1] for row in source)
    need(counts == {'*':46,'+':20,'-':17}, 'ledger')
    need(len(packet['witnesses']) == 18, 'witness count')
    # Independent factorial valuations, not the author's binomial recurrence.
    coefficient_cases = guarded_cases = 0
    for r in range(25, 512, 2):
        p = r.bit_count()
        k, ell, h = valuation(r+1), valuation(r+3), valuation(r-1)
        values = [factorial_v2(2*r)-factorial_v2(r+j)-factorial_v2(r-j)
                  for j in range(4)]
        need(values == [p,p-k,p+h-k,p+h-k-ell], 'four valuations')
        coefficient_cases += 1
        for t in range(4, 10):
            if max(k,ell) > t-2:
                continue
            need(all(values[j]+j*t > p for j in (1,2,3)), 'strict central minimum')
            cubic = sum(comb(2*r,r+j)*(-2**t)**j for j in range(4))
            need(valuation(cubic) == p, 'central valuation')
            guarded_cases += 1
    # The exact inverse-population equality includes S=Lambda.
    population_cases = 0
    for n in range(2, 9):
        Lambda = 2**n
        for S in range(1,Lambda+1):
            for T in range(1,Lambda-1):
                value = (Lambda-S)*(Lambda-1)+T
                bound = n+T.bit_count()
                need(value.bit_count() <= bound, 'population upper bound')
                need((value.bit_count() == bound) == (S<Lambda and S&T == 0),
                     'population equality iff AND zero')
                population_cases += 1
    # Exact t-bit complement after the added origin bit, independently of typing.
    complement_cases = 0
    for t in range(4, 11):
        q = 2**t
        for A in range(2,q-1,2):
            D = q-1-A
            need((q-1) ^ (A+1) == D-1, 'origin complement')
            complement_cases += 1
    return {
      'reviewer_sha256':sha(Path(__file__).read_bytes()),
      'author_pins':AUTHOR, 'dependency_pins':PINS,
      'source':{'named_outer_rows_guarded':len(OUTER),'rows_recounted':83,
                'multiplications':46,'additions_subtractions':37,'witnesses':18},
      'fresh_checks':{'four_coefficient_valuation_sets':coefficient_cases,
                      'guarded_cubic_cases':guarded_cases,
                      'inverse_population_cases':population_cases,
                      'origin_complement_cases':complement_cases},
      'scope':{'proof_review':'conditional dyadic negative-W exclusion on valid compiler slices',
               'author_or_predecessor_execution':False,'prior_source_evaluation':False,
               'new_native_tuple_materialized':False,'new_universal_bound':False,
               'unresolved':['nondyadic q','u>=t with W=0']}}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--author',type=Path,required=True)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write',type=Path)
    group.add_argument('--expect',type=Path)
    args = parser.parse_args()
    result = inspect(args.root,args.author)
    text = json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.write:
        with args.write.open('x') as f:
            f.write(text)
    else:
        need(args.expect.read_text() == text, 'exact independent receipt')
    print(json.dumps(result['fresh_checks'],sort_keys=True))

if __name__ == '__main__':
    main()
