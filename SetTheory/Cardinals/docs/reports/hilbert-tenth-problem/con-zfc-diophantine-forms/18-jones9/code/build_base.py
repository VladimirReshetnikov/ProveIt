"""Exact normalized quartic and a division-free bound for its Jones index.

All sparse arithmetic is over Z[n_1,...,n_32,beta,K0,MC,MF].  The fixed
coefficient ports are kept symbolic: their enormous decimal expansions
are neither required nor attempted.  Python standard library only.
"""
from collections import defaultdict
from itertools import product
from math import comb, factorial
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def add(p, q):
    out = defaultdict(int, p)
    for e, c in q.items():
        out[e] += c
    return {e: c for e, c in out.items() if c}

def mul(p, q):
    out = defaultdict(int)
    for e, c in p.items():
        for f, d in q.items():
            out[tuple(a+b for a,b in zip(e,f))] += c*d
    return {e: c for e,c in out.items() if c}

def shift(p, n):
    """Substitute x_j=n_j+1 for the first n coordinates, exactly."""
    out = defaultdict(int)
    for e,c in p.items():
        active = [(j,a) for j,a in enumerate(e[:n]) if a]
        for choices in product(*(range(a+1) for j,a in active)):
            f = [0]*n + list(e[n:])
            d = c
            for (j,a), k in zip(active, choices):
                f[j] = k
                d *= comb(a,k)
            out[tuple(f)] += d
    return {e:c for e,c in out.items() if c}

def evaluate(p, values, modulus=None):
    ans = 0
    for e,c in p.items():
        v = c
        for a,k in zip(values,e):
            if k:
                v *= pow(a,k,modulus) if modulus else a**k
                if modulus:
                    v %= modulus
        ans += v
    return ans % modulus if modulus else ans

def records(p):
    return [{'powers':list(e), 'coefficient':c} for e,c in sorted(p.items())]

def build():
    source = json.loads((ROOT/'base/quartic32.upstream.json').read_text())
    n = len(source['variables'])
    require(n == 32, 'Expected 32 witnesses')
    raw = [{tuple(t['powers']): t['coefficient'] for t in eq['terms']}
           for eq in source['equations']]
    require(len(raw) == 23, 'Expected 23 residuals')
    shifted = [shift(r,n) for r in raw]
    poly = {}
    for r in shifted:
        poly = add(poly,mul(r,r))
    require(max(sum(e[:n]) for e in poly)==4, 'Quartic degree mismatch')
    # The fifth residual is E-X(a-E), which is 1 at all original variables 1.
    e_index = source['variables'].index('E')
    x_index = source['variables'].index('X')
    a_index = source['variables'].index('a')
    require([e_index,x_index,a_index] == [17,21,20], 'Witness ordering mismatch')
    constant_r5 = {e[n:]:c for e,c in shifted[4].items() if not any(e[:n])}
    require(constant_r5 == {(0,0,0,0):1}, 'Normalization residual mismatch')
    tau_index=source['variables'].index('tau')
    tau_monomial=tuple(4 if j==tau_index else 0 for j in range(n+4))
    require(poly.get(tau_monomial)==1, 'Quartic leading coefficient mismatch')

    # ||r(n+1)||_1 <= rho.  Thus ||sum r(n+1)^2||_1 <= sum rho^2.
    rhos=[]
    for r in raw:
        rho=defaultdict(int)
        for e,c in r.items():
            rho[e[n:]] += abs(c)*(2**sum(e[:n]))
        rhos.append(dict(rho))
    bound={(0,0,0,0):2}
    for rho in rhos:
        bound=add(bound,{e:24*c for e,c in mul(rho,rho).items()})

    grouped=defaultdict(dict)
    for e,c in poly.items():
        grouped[e[:n]][e[n:]]=c
    code=[]
    for exponent,coeff in sorted(grouped.items()):
        slack=4-sum(exponent)
        multiplier=factorial(slack)
        for k in exponent:
            multiplier*=factorial(k)
        require(1<=multiplier<=24, 'Invalid factorial multiplier')
        # x is the dummy input, exponent zero; witness j is digit position 5^(j+1).
        code.append({'witness_powers':list(exponent),
                     'position':sum(k*5**(j+1) for j,k in enumerate(exponent)),
                     'factorial_multiplier':multiplier,
                     'coefficient':records(coeff)})

    out={'description':'P(x,n)=sum of 23 shifted quadratic residual squares; x unused',
         'witnesses':['n_'+v for v in source['variables']],
         'fixed_ports':source['constants'], 'degree':4,
         'normalization_certificate':'Residual 5 is 1 when every n-coordinate is zero',
         'coefficient_ring_order':source['constants'],
         'coding_nu':n, 'coding_delta':4, 'coding_L':5**(n+1),
         'star_cardinality':comb(n+5,4),
         'nonzero_coefficient_count':len(code),
         'coefficients':code}
    (ROOT/'base/normalized_quartic32.json').write_text(json.dumps(out,indent=2)+'\n')
    bound_out={'definition':'s=2+24*sum_j rho_j^2; z=2^s',
               'rho_definition':'sum_raw_terms |c|*2^(witness_degree)*fixed_ports^powers',
               'fixed_port_order':source['constants'], 's_terms':records(bound),
               'rho_terms':[records(rho) for rho in rhos],
               'proof':'Positive fixed ports imply s >= 2+sum_{k in star}|P_k|, hence |P_k|+1<2^s.'}
    (ROOT/'base/index_bound_s.json').write_text(json.dumps(bound_out,indent=2)+'\n')

    checks=[]
    for ports in [(15,17,2,19),(31,123,6,44),(1,1,1,1),(2,3,5,7)]:
        vals=[0]*n+list(ports)
        p0=evaluate(poly,vals)
        require(p0>=1, 'Normalization check failed')
        s=evaluate(bound,ports)
        total=sum(row['factorial_multiplier']*abs(evaluate(grouped[tuple(row['witness_powers'])],ports))
                  for row in code)
        require(s>=2+total, 'Coefficient majorant check failed')
        checks.append({'ports':ports,'P_at_zero':p0,'s':s,'sum_abs_scaled_coefficients':total})
    # Independent numeric checks of the affine substitution and SOS expansion.
    for seed in range(25):
        vals=[((j+1)*(seed+3)%9)-4 for j in range(n)]+[15+seed,7+seed,2+seed,21+seed]
        rawvals=[v+1 for v in vals[:n]]+vals[n:]
        direct=sum(evaluate(r,rawvals)**2 for r in raw)
        require(evaluate(poly,vals)==direct, 'Affine substitution identity failed')
    receipt={'status':'PASS','residual_count':23,'witness_count':n,
             'formal_sparse_terms':len(poly),'nonzero_witness_monomials':len(code),
             'degree':4,'index_bound_term_count':len(bound),
             'normalized_at_zero':True,'tau_fourth_power_coefficient':1,
             'signed_affine_substitution_checks':25,'small_port_index_checks':checks,
             'source_sha256':hashlib.sha256((ROOT/'base/quartic32.upstream.json').read_bytes()).hexdigest(),
             'scope':'Exact finite polynomial checks; no claim to check K215 consistency or rerun Lean.'}
    (ROOT/'verification/base.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
    return out,bound_out

if __name__=='__main__':
    build()
