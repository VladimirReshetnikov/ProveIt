#!/usr/bin/env python3
"""Read-only independent checks supporting the direct C222 ordinary review.

This never imports/executes an intake program or compiles Lean.  Small Horn
examples test the generic flow lemma, not the existence of a ZFC refutation.
"""
import collections
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
DEFAULT = Path('/tmp/dioph-wave12-arrivals-43ac596e36/con-zfc-direct-and-centered-round12')


def need(ok, text):
    if not ok:
        raise RuntimeError(text)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def load(path):
    return json.loads(path.read_text())


def product_poly(labels):
    result = [1]
    for label in labels:
        after = result + [0]
        for i,c in enumerate(result):
            after[i+1] += c*label
        result = after
    return result


def crt(residues, moduli):
    product = math.prod(moduli)
    return sum(r*(product//d)*pow(product//d,-1,d)
               for r,d in zip(residues,moduli)) % product


def main():
    home = Path(sys.argv[1]) if len(sys.argv)>1 else DEFAULT
    arrival = load(home.parent/'ARRIVAL.json')
    archive = REPO/arrival['archive']
    need(sha(archive.read_bytes()) == arrival['sha256'], 'round12 actual ZIP pin')
    arithmetic = load(home/'direct/SOURCE_PINS.json')
    for name,digest in arithmetic['sources'].items():
        need(sha((home/'direct/sources'/name).read_bytes()) == digest, 'arithmetic source SHA256')
    source = load(home/'direct_audit/SOURCE_PINS.json')
    for item in source['sources']:
        raw = (home/'direct_audit/sources'/item['name']).read_bytes()
        need(sha(raw) == item['sha256'] and len(raw) == item['bytes'], 'calculus source SHA256/length')
        need(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest() == item['sha'], 'calculus source Git blob')
    horn_path = home/'direct/fixed_base/horn_shared_source.json'
    need(sha(horn_path.read_bytes()) == arithmetic['inherited_horn_sha256'], 'complete fixed Horn source pin')
    horn = load(horn_path)
    branch_names = ['truth','rho1','rho2','rho3','rho4','rho5','rho6','growG','rho8','bundle','mp','gen']
    need([b['name'] for b in horn['branches']] == branch_names and
         horn['witness_count'] == 17 and horn['common_wire_count'] == 13 and
         horn['base_witnesses'] == ['a','b','c','d'], 'twelve shared Horn branches')
    endpoint = (home/'direct_audit/sources/KEndpoint.lean').read_text()
    choice = (home/'direct_audit/sources/ConstructibleChoice.lean').read_text()
    need('theorem c222_iff_zf_refutation : KCode222.C222 Code254.F ↔ BProv ZFax_s [] Form.fBot :=' in endpoint,
         'actual unconditional calculus endpoint declaration')
    need('theorem zf_refutation_iff_zfc_refutation :' in choice and
         'BProv ZFax_s [] Form.fBot ↔ BProv ZFCax_s [] Form.fBot :=' in choice,
         'actual choice transport declaration')

    # All finite single-conclusion instances on labels0,1,2, including cycles
    # and repeated premises. Check every multiset of at most three rules.
    universe = list(itertools.product(range(3),repeat=3))
    flow_cases, balanced_cases = 0,0
    for n in range(4):
        for selected in itertools.combinations_with_replacement(universe,n):
            balance = [0,0,0]
            for p,q,c in selected:
                if c: balance[c] += 1
                if p: balance[p] -= 1
                if q: balance[q] -= 1
            derived = {0}
            while True:
                after = derived | {c for p,q,c in selected if p in derived and q in derived}
                if after == derived: break
                derived = after
            if balance == [0,1,0]:
                need(1 in derived, 'generic finite flow implies derivability control')
                balanced_cases += 1
            flow_cases += 1
    # A cyclic self-loop cannot supply the missing net target occurrence.
    need([(1 if c==1 else 0)-(1 if p==1 else 0)-(1 if q==1 else 0)
          for p,q,c in [(1,0,1)]] == [0], 'self-loop negative control')

    height_cases = 0
    for m in range(3):
        triples = list(itertools.product(range(m+1),repeat=3))
        for n in range(4):
            for selected in itertools.product(triples,repeat=n):
                aa = product_poly([c for p,q,c in selected])
                bb = product_poly([1]+[v for p,q,c in selected for v in [p,q]])
                aa += [0]*(len(bb)-len(aa))
                height = 1 << (2*m*n+1)
                need(all(abs(a-b) <= height for a,b in zip(aa,bb)), 'fixed binary coefficient bound control')
                height_cases += 1

    # One completely explicit beta trace for the abstract axiom0,0->1.
    # This is a toy Horn instance, never an asserted C222 refutation.
    n,m = 1,1
    m0 = 1 << (2*m*n+1)
    carrier = m0+1
    trace = [carrier+1,1]
    radix = 11
    beta_moduli = [1+(i+1)*radix for i in range(n+1)]
    code = crt(trace,beta_moduli)
    need([code%d for d in beta_moduli] == trace and
         trace[1]*(1+carrier) == trace[0], 'toy one-stream beta completeness')

    # A genuine two-column uniform-bound CRT certificate for the polynomial
    # row w1+w2=3*i+3 on i=0,1,2.  Explicitly recompute T after choosing U.
    N,U = 3,5
    factorial_argument = 2*U+(3*N+3)+N
    T = math.factorial(factorial_argument)
    ds = [1+(j+1)*T for j in range(N)]
    B = math.prod(ds)
    index = crt(list(range(N)),ds)
    coords = [crt([j+2 for j in range(N)],ds),crt([2*j+1 for j in range(N)],ds)]
    need(all(math.gcd(ds[i],ds[j]) == 1 for i in range(N) for j in range(i)), 'CRT pairwise coprime')
    need((1+(index+1)*T)%B == 0 and (sum(coords)-(3*index+3))%B == 0, 'CRT encoded index/row')
    need(all(math.factorial(U+1)*math.comb(a,U+1)%B == 0 for a in coords), 'CRT common falling-factorial bound')
    Q = (1+(N+1)*T)**N+2
    encoded_product = (T**N*math.factorial(N)*math.comb(Q+N,N))%(T*Q-1)
    need(encoded_product == B, 'explicit product-as-remainder control')

    natural_summary = load(home/'direct/fixed_base/summary_affine.json')
    integer_summary = load(home/'direct/fixed_base/summary_integer.json')
    equation_path = home/'direct/fixed_base/equation_integer.json'
    equation = load(equation_path)
    terms,seen,used = equation['terms'],set(),set()
    for coefficient,monomial in terms:
        need(type(coefficient) is int and coefficient != 0 and len(monomial) <= 4,
             'literal nonzero quartic integer term')
        need(monomial == sorted(monomial) and all(type(i) is int and 0<=i<27916 for i in monomial), 'valid literal monomial indices')
        key = tuple(monomial)
        need(key not in seen, 'collected support has no duplicate')
        seen.add(key);used.update(monomial)
    need(equation['variable_count'] == 27916 and len(terms) == 758275 and
         max(len(m) for c,m in terms) == 4 and
         max(abs(c) for c,m in terms) == 320307372009918 and
         len(used) == 27916, 'fully materialized integer metrics/all variables live')
    need(natural_summary['ordinary_polynomial_variables'] == 16036 and
         natural_summary['input_existentials'] == 3960 and
         natural_summary['nonlinear_wires'] == 12076 and
         natural_summary['SOS_residuals'] == 12366 and
         integer_summary['ordinary_polynomial_variables'] == 16036+3*3960,
         'affine/integer conversion dimension identity')
    vals = {a*a+b*b+c*(c+1) for a in range(17) for b in range(17) for c in range(17)}
    need(all(n in vals for n in range(257)), 'bounded three-square guard completeness control')
    result = dict(status='PASS', python_optimization=sys.flags.optimize, arrival=arrival,
                  authenticated_arithmetic_sources=len(arithmetic['sources']),
                  authenticated_calculus_sources=len(source['sources']),
                  unconditional_endpoint_declarations_present=True, horn_branches=branch_names,
                  generic_flow_multiset_controls=flow_cases, balanced_controls=balanced_cases,
                  fixed_binary_height_controls=height_cases,
                  exact_toy_beta_trace=dict(N=n,max_label=m,M0=m0,M=carrier,y=radix,x=code),
                  exact_two_column_CRT_certificate=True, natural_summary=natural_summary,
                  integer_summary=integer_summary, full_integer_literal_sha256=sha(equation_path.read_bytes()),
                  actual_integer_terms_scanned=len(terms), all_integer_variables_live=True,
                  scope='Ordinary proof/calculus/interface review in companion note, selected independent structural/finite controls; no intake execution, Lean compilation, internal-ZFC proof, or new proof of the named Pell theorems.')
    out=ROOT/'PROPOSAL_REVIEW_DIRECT_C222_ROUND12.json'
    if sys.flags.optimize:out=out.with_name(out.stem+'_OPTIMIZED.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS direct C222 source pins, generic flow/height/CRT controls and literal quartic metrics')


if __name__=='__main__':main()
