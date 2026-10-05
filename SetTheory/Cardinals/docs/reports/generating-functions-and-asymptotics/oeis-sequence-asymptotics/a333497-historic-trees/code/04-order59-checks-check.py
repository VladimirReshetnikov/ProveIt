#!/usr/bin/env python3
"""Exact d=30 finite certificate; the accompanying analytic proof is separate."""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from math import factorial, prod
from pathlib import Path
import re
import stat
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
MAX_FILE = 256 * 1024

class CheckFailure(Exception):
    def __init__(self, name, detail):
        self.name, self.detail = name, str(detail)
        super().__init__(f'{name}: {detail}')

def need(condition, name, detail):
    # Explicit guards, never assert: python -O must not disable any check.
    if not condition:
        raise CheckFailure(name, detail)

def exact_json(path, name):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            need(key not in result, name, f'duplicate key {key}')
            result[key] = value
        return result
    def bad(token):
        raise CheckFailure(name, f'non-integer JSON number {token}')
    def integer(token):
        need(len(token) <= 10, name, 'JSON integer exceeds schema bound')
        return int(token)
    try:
        need(path.stat().st_size <= MAX_FILE, name, 'file exceeds 256 KiB bound')
        return json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=unique,
                          parse_constant=bad, parse_float=bad, parse_int=integer)
    except CheckFailure:
        raise
    except (OSError, ValueError, UnicodeError, RecursionError) as error:
        raise CheckFailure(name, error) from None

def rational(value, name):
    need(type(value) is str and len(value) <= 1024 and
         re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?', value) is not None,
         name, 'expected bounded canonical rational string')
    result = F(value)
    need(str(result) == value, name, 'rational string is not reduced/canonical')
    return result

def integer_string(value, name):
    result = rational(value, name)
    need(result.denominator == 1, name, 'expected integer string')
    return result.numerator

def keys(obj, expected, name):
    need(type(obj) is dict and set(obj) == set(expected), name, 'missing or unexpected object fields')

def safe_path(name):
    return (type(name) is str and bool(name) and not name.startswith('/') and
            '\\' not in name and '\n' not in name and '\r' not in name and
            '..' not in Path(name).parts and Path(name).as_posix() == name and name != '.')

def inventory(root):
    result = {}
    for path in sorted(root.rglob('*')):
        name = path.relative_to(root).as_posix()
        mode = path.lstat().st_mode
        need(not stat.S_ISLNK(mode), 'INTEGRITY_SYMLINK', name)
        need(stat.S_ISDIR(mode) or stat.S_ISREG(mode), 'INTEGRITY_SPECIAL_FILE', name)
        need(safe_path(name), 'INTEGRITY_PATH', name)
        if stat.S_ISREG(mode):
            need(path.stat().st_size <= MAX_FILE, 'INTEGRITY_SIZE', name)
            result[name] = sha256(path.read_bytes()).hexdigest()
    need(len(result) <= 32, 'INTEGRITY_SIZE', 'too many files')
    return result

def manifest_check(root):
    actual = inventory(root)
    need('MANIFEST.json' in actual, 'INTEGRITY_MISSING', 'MANIFEST.json')
    obj = exact_json(root/'MANIFEST.json', 'INTEGRITY_MANIFEST')
    keys(obj, {'format', 'files'}, 'INTEGRITY_MANIFEST')
    need(type(obj['format']) is int and obj['format'] == 1, 'INTEGRITY_MANIFEST', 'expected format 1')
    expected = obj['files']
    need(type(expected) is dict and 0 < len(expected) <= 31, 'INTEGRITY_MANIFEST', 'invalid files map')
    for name, digest in expected.items():
        need(safe_path(name) and name != 'MANIFEST.json', 'INTEGRITY_MANIFEST', 'unsafe/self path')
        need(type(digest) is str and re.fullmatch('[0-9a-f]{64}', digest) is not None,
             'INTEGRITY_MANIFEST', 'invalid SHA-256')
        need(name in actual, 'INTEGRITY_MISSING', name)
        need(actual[name] == digest, 'INTEGRITY_HASH', name)
    actual.pop('MANIFEST.json')
    need(set(actual) == set(expected), 'INTEGRITY_UNLISTED', sorted(set(actual)-set(expected)))
    return len(expected)

def add(p, q):
    result = [0]*max(len(p), len(q))
    for i, c in enumerate(p): result[i] += c
    for i, c in enumerate(q): result[i] += c
    return trim(result)

def trim(p):
    while len(p) > 1 and p[-1] == 0: p.pop()
    return p

def mul(p, q):
    result = [0]*(len(p)+len(q)-1)
    for i, c in enumerate(p):
        for j, b in enumerate(q): result[i+j] += c*b
    return trim(result)

def evaluate(p, x):
    value = 0
    for c in reversed(p): value = value*x+c
    return value

def product_polynomial(first, last):
    p = [1]
    for a in range(first, last+1): p = mul(p, [a, 1])
    return p

def sparse_characteristic(d, A):
    """Leibniz determinant of lambda I-B: enumerate actual nonzero permutations."""
    terms = []
    def visit(row, used, columns, factor):
        if row == d:
            inversions = sum(columns[i] > columns[j] for i in range(d) for j in range(i+1,d))
            terms.append([(-1 if inversions % 2 else 1)*c for c in factor])
            return
        for col, polynomial in [(row, [d+row,1]), ((row+1)%d, [-1 if row<d-1 else -2*A])]:
            if col not in used: visit(row+1, used|{col}, columns+[col], mul(factor,polynomial))
    visit(0, set(), [], [1])
    need(len(terms) == 2, 'CHARACTERISTIC_DETERMINANT', 'cyclic matrix must have exactly two nonzero permutation terms')
    return add(*terms)

def routh(poly):
    """Ordinary unscaled rational Routh array; no floating-point root finding."""
    descending = list(map(F, reversed(poly)))
    degree = len(poly)-1
    width = (degree+2)//2
    rows = [descending[0::2], descending[1::2]]
    rows = [r+[F(0)]*(width-len(r)) for r in rows]
    for k in range(2,degree+1):
        top, bottom = rows[-2:]
        need(bottom[0] != 0, 'ROUTH_PIVOT', f'row {k-1}')
        row = [(bottom[0]*top[j+1]-top[0]*bottom[j+1])/bottom[0]
               for j in range(width-1)]+[F(0)]
        need(any(row), 'ROUTH_ZERO_ROW', f'row {k}')
        rows.append(row)
    need(all(row[0] != 0 for row in rows), 'ROUTH_PIVOT', 'zero first-column entry')
    signs = [1 if row[0]>0 else -1 for row in rows]
    return signs, sum(a!=b for a,b in zip(signs,signs[1:]))

def seven(values):
    A,R,I,S,lo,hi,mod10,hi10 = (values[k] for k in ('A','R','I','S','phase_lower','phase_upper','modulus_squared_at_10','phase_upper_at_10'))
    tests = [('REAL_POSITIVE',R>0), ('IMAG_POSITIVE',I>0),
             ('MODULUS_Q',R*R+I*I<4*S*S), ('PHASE_Q_LOWER',lo>6),
             ('PHASE_Q_UPPER',hi<7), ('MODULUS_10',mod10>4*A*A), ('PHASE_10_UPPER',hi10<8)]
    for label, passed in tests: need(passed, 'INEQUALITY_'+label, 'required strict inequality failed')
    return [label for label,_ in tests]

MODEL = {'derivative_order':30, 'paper_parameter_m':29, 'btree_order':59,
         'first_factor':30, 'last_factor':59, 'first_coordinate':0, 'last_coordinate':29}
PHASE_KEYS = {'q','upper_omega','A','R','I','S','phase_lower','phase_upper','modulus_squared_at_10','phase_upper_at_10'}
ALGEBRA_KEYS = {'characteristic_ascending','quotient_ascending','routh_signs','coefficient_multiplier','real_roots','unstable_winding_indices','stable_winding_indices','full_right','full_left','full_axis','quotient_right','quotient_left','quotient_axis'}

def read_fixture(root):
    obj = exact_json(root/'fixtures/certificate.json', 'FIXTURE_JSON')
    keys(obj, {'schema_version','model','phase','algebra'}, 'FIXTURE_SCHEMA')
    need(type(obj['schema_version']) is int and obj['schema_version']==1, 'FIXTURE_VERSION', 'expected version 1')
    keys(obj['model'], MODEL, 'MODEL_SCHEMA')
    for key, value in obj['model'].items():
        need(type(value) is int and value == MODEL[key], 'MODEL_'+key.upper(), 'fixed d=30 model/index does not match')
    keys(obj['phase'], PHASE_KEYS, 'PHASE_SCHEMA')
    phase = {key:rational(value, 'PHASE_VALUE_SCHEMA') for key,value in obj['phase'].items()}
    for key in ('upper_omega','A','R','I','S','modulus_squared_at_10'):
        need(phase[key].denominator==1, 'PHASE_VALUE_SCHEMA', f'{key} must be an integer')
    need(phase['q']==F(911,100) and phase['upper_omega']==10, 'PHASE_INPUT', 'certificate uses q=911/100 and upper omega=10')
    alg = obj['algebra']; keys(alg, ALGEBRA_KEYS, 'ALGEBRA_SCHEMA')
    for key, length in [('characteristic_ascending',31),('quotient_ascending',30),('real_roots',2)]:
        need(type(alg[key]) is list and len(alg[key])==length, 'ALGEBRA_ARRAY_SCHEMA', f'{key} length')
        alg[key] = [integer_string(x,'ALGEBRA_VALUE_SCHEMA') for x in alg[key]]
    alg['coefficient_multiplier'] = integer_string(alg['coefficient_multiplier'],'ALGEBRA_VALUE_SCHEMA')
    for key, length in [('routh_signs',30),('unstable_winding_indices',1),('stable_winding_indices',13)]:
        need(type(alg[key]) is list and len(alg[key])==length and all(type(x) is int for x in alg[key]),
             'ALGEBRA_ARRAY_SCHEMA', f'{key} length/type')
    for key in ('full_right','full_left','full_axis','quotient_right','quotient_left','quotient_axis'):
        need(type(alg[key]) is int and 0 <= alg[key] <= 30, 'ALGEBRA_COUNT_SCHEMA', key)
    return obj, phase, alg

def compute_phase():
    A = prod(range(30,60)); q = F(911,100)
    # Gaussian-integer pair multiplication of product(100*a+911*i).
    R,I = 1,0
    for a in range(30,60): R,I = 100*a*R-911*I, 911*R+100*a*I
    S = 100**30*A
    # Independent polynomial representation: evaluate product(a+x) at x=i*q.
    polynomial = product_polynomial(30,59)
    real = sum(F(polynomial[j])*(-1)**(j//2)*q**j for j in range(0,31,2))
    imag = sum(F(polynomial[j])*(-1)**((j-1)//2)*q**j for j in range(1,31,2))
    need(real*100**30==R and imag*100**30==I, 'GAUSSIAN_TWO_METHODS', 'integer product and rational polynomial evaluation differ')
    return {'q':q,'upper_omega':F(10),'A':F(A),'R':F(R),'I':F(I),'S':F(S),
            'phase_lower':sum((q/a-(q/a)**3/3 for a in range(30,60)),F(0)),
            'phase_upper':sum((q/a for a in range(30,60)),F(0)),
            'modulus_squared_at_10':F(prod(a*a+100 for a in range(30,60))),
            'phase_upper_at_10':sum((F(10,a) for a in range(30,60)),F(0))}

def run(root=ROOT, skip_integrity=False):
    files = manifest_check(root) if not skip_integrity else None
    obj, phase, alg = read_fixture(root)
    seven(phase)  # Detect each strict boundary failure before equality comparison.
    computed = compute_phase()
    for key in sorted(PHASE_KEYS): need(phase[key]==computed[key], 'PHASE_FIELD_'+key.upper(), 'fixture differs from independent exact reconstruction')
    inequalities = seven(computed)
    d=30; A=int(computed['A']); P=product_polynomial(30,59); P[0]-=2*A
    need(alg['characteristic_ascending']==P,'CHARACTERISTIC_FIXTURE','ascending coefficients differ')
    need(sparse_characteristic(d,A)==P,'CHARACTERISTIC_DETERMINANT','det(lambda I-B) differs')
    need(evaluate(P,1)==0 and evaluate(P,-90)==0,'REAL_ROOT_IDENTITIES','endpoint root not exact')
    derivative=[j*P[j] for j in range(1,len(P))]
    need(evaluate(derivative,1)!=0 and evaluate(derivative,-90)!=0,'REAL_ROOT_SIMPLICITY','endpoint derivative vanished')
    # Divide by lambda-1 from the constant end, then verify by full multiplication.
    Q=[-P[0]]
    for j in range(1,d): Q.append(Q[-1]-P[j])
    need(mul(Q,[-1,1])==P,'TRANSLATION_DIVISION','polynomial division identity failed')
    need(alg['quotient_ascending']==Q,'QUOTIENT_FIXTURE','quotient coefficients differ')
    # Eigenvector polynomial identities, valid simultaneously at every root of P.
    vectors=[[1]]
    for j in range(1,d): vectors.append(mul(vectors[-1],[d+j-1,1]))
    for j in range(d-1):
        need(add(vectors[j+1],[-c for c in mul(vectors[j],[d+j,1])])==[0],
             'EIGENVECTOR_RECURRENCE', f'coordinate {j}')
    need(add(mul(vectors[-1],[59,1]),[-2*A])==P,'EIGENVECTOR_CLOSURE','last coordinate residual differs from P')
    at_one=[evaluate(v,1) for v in vectors]; at_minus=[evaluate(v,-90) for v in vectors]
    need(all(v>0 for v in at_one),'POSITIVE_REAL_MODE','root 1 eigenvector not positive')
    need(all(v*(-1)**j>0 for j,v in enumerate(at_minus)),'ALTERNATING_REAL_MODE','root -90 signs do not alternate')
    need(alg['real_roots']==[-90,1],'REAL_ROOT_INDEX','real-root list differs')
    coefficient_multiplier=F(A,factorial(29))
    need(coefficient_multiplier==F(factorial(59),factorial(29)**2), 'MODEL_NORMALIZATION','paper and pole prefactors differ')
    need(alg['coefficient_multiplier']==coefficient_multiplier,'COEFFICIENT_MULTIPLIER','paper conjecture prefactor differs')
    for n in (0,1,2,10,100):
        pole_derivative=A*prod(range(d,d+n))
        paper_coefficient=coefficient_multiplier*factorial(n+29)
        need(pole_derivative==paper_coefficient,'COEFFICIENT_INDEXING',f'n={n}')
    # Elementary rational comparisons accompanying the analytic use of 3<pi<22/7.
    need(F(3,2)*F(22,7)<6 and 7<F(5,2)*3 and 8<4*3,
         'PHASE_WINDOW_LOGIC','rational phase-window comparisons failed')
    need(F(1994,1000)<computed['R']/computed['S']<F(1995,1000) and
         F(49,10000)<computed['I']/computed['S']<F(50,10000),
         'PRODUCT_READER_ENCLOSURES','exact illustrative enclosures failed')
    signs,changes=routh(Q)
    need(signs==[1]*28+[-1,1] and changes==2,'ROUTH_COUNT','unexpected exact Routh count')
    need(alg['routh_signs']==signs,'ROUTH_SIGNS_FIXTURE','stored signs differ')
    expected_counts={'full_right':3,'full_left':27,'full_axis':0,'quotient_right':2,'quotient_left':27,'quotient_axis':0}
    for key,value in expected_counts.items(): need(alg[key]==value,'COUNT_'+key.upper(),'root count differs')
    # These lists encode the report's analytic strictly decreasing winding order.
    need(alg['unstable_winding_indices']==[1],'UNSTABLE_WINDING_INDEX','unstable pair must have winding index 1')
    need(alg['stable_winding_indices']==list(range(2,15)),'STABLE_WINDING_INDEX','stable pairs must have winding indices 2 through 14')
    return {'status':'PASS','kind':'EXACT_FINITE_CERTIFICATE','arithmetic':'Python integers and fractions.Fraction only',
            'model':obj['model'],'integrity_checked':not skip_integrity,'sealed_files':files,
            'seven_inequalities':inequalities,'gaussian_product_independent_methods':2,
            'characteristic_degree':30,'matrix_determinant_nonzero_permutation_terms':2,
            'eigenvector_polynomial_identities':30,'coefficient_index_samples':[0,1,2,10,100],
            'routh_quotient_signs':''.join('+' if x>0 else '-' for x in signs),'routh_sign_changes':changes,
            'spectral_counts':expected_counts,'unstable_winding_indices':[1],'stable_winding_indices':list(range(2,15)),
            'scope':'Finite arithmetic and polynomial identities. The phase-curve ordering, cyclic cone, stable-subspace exclusion, stable-manifold theorem and Abelian implication are analytic arguments in the report. No floating-point root finding, replacement asymptotic, first-transition or novelty claim is certified.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-integrity',action='store_true',help='development only; not sealed-bundle verification')
    parser.add_argument('--output',type=Path,help='optional JSON result outside the sealed checks directory')
    args=parser.parse_args()
    try:
        if args.output: need(not args.output.resolve().is_relative_to(ROOT),'OUTPUT_LOCATION','output must be outside checks directory')
        result=run(skip_integrity=args.skip_integrity)
        text=json.dumps(result,indent=2,sort_keys=True)+'\n'
        if args.output: args.output.write_text(text,encoding='utf-8')
        else: print(text,end='')
    except CheckFailure as error:
        print(json.dumps({'status':'FAIL','diagnostic':error.name,'detail':error.detail},indent=2)); return 1
    except Exception as error:
        print(json.dumps({'status':'ERROR','diagnostic':'CHECK_EXCEPTION','detail':f'{type(error).__name__}: {error}'},indent=2)); return 2
    return 0
if __name__=='__main__': sys.exit(main())
