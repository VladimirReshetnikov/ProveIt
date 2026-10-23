#!/usr/bin/env python3
"""Exact audit of direct one-coordinate eliminations, not an optimality proof.

Reads pinned JSON as data. Does not execute any upstream code.
Requires Python 3 and SymPy.
"""
import hashlib
import json
from pathlib import Path
import sympy as S

ROOT = Path(__file__).resolve().parent
PIN = '22e75dd6b87b1b199bb08c778d7cf075ae5aae08'

def require(condition, message):
    if not condition:
        raise ValueError(message)

def save(name, obj):
    (ROOT / name).write_text(json.dumps(obj, indent=2) + '\n')

source_path = ROOT / 'sources/31-sun10__quartic31__quartic31_system60.json'
source = json.loads(source_path.read_text())
variables = S.symbols(' '.join(source['variables']))
constants = S.symbols(' '.join(source['constants']))
env = dict(zip(source['variables'] + source['constants'], variables + constants))
original_env = dict(env)

def val(x):
    return S.Integer(x) if isinstance(x, int) else env[x]

for target, op, a, b in source['source']:
    lhs, rhs = val(a), val(b)
    env[target] = {'+': lambda: lhs+rhs, '-': lambda: lhs-rhs, '*': lambda: lhs*rhs}[op]()
residuals = [S.expand(val(a)-val(b)) for a,b in source['comparisons']]
require(len(variables) == 31 and len(residuals) == 22, 'unexpected parent dimension')
require(all(S.Poly(r,*variables).total_degree()==2 for r in residuals), 'nonquadratic parent')

records = []
for defining_index, residual in enumerate(residuals):
    for variable in variables:
        p = S.Poly(residual, variable)
        if p.degree() != 1 or p.nth(1) not in (-1,1):
            continue
        replacement = S.expand(-p.nth(0)/p.nth(1))
        remaining = [v for v in variables if v != variable]
        converted = [(j+1,S.Poly(S.expand(r.subs(variable,replacement)),*remaining))
                     for j,r in enumerate(residuals) if j != defining_index]
        max_degree = max(poly.total_degree() for _,poly in converted)
        require(max_degree > 2, 'unexpected quartic-preserving direct elimination')
        certificate = None
        for equation, poly in converted:
            for monomial, coefficient in poly.terms():
                if sum(monomial) != max_degree:
                    continue
                cp = S.Poly(coefficient,*constants)
                cfs = cp.coeffs()
                if all(c>0 for c in cfs) or all(c<0 for c in cfs):
                    certificate = dict(equation=equation,
                         monomial={str(v):e for v,e in zip(remaining,monomial) if e},
                         coefficient=str(coefficient),
                         nonvanishing='All coefficients have the same nonzero sign; all four ports are positive.')
                    break
            if certificate:
                break
        require(certificate is not None,'missing uniform leading certificate')
        records.append(dict(eliminated=str(variable),defining_equation=defining_index+1,
                    replacement=str(replacement),remaining_variables=30,remaining_equations=21,
                    maximum_residual_degree=max_degree,sos_exact_degree=2*max_degree,
                    equations_above_degree_two=[eq for eq,p in converted if p.total_degree()>2],
                    leading_certificate=certificate))

# Exact identity for the only promising rational transport elimination.
e = original_env
q = e['beta']*e['J']+1
C = q-e['F']-e['alpha']
w, X, L, z = (e[x] for x in ('w','X','L','z'))
t = (e['K0']+w)*C-e['F']-z*(q-1)
t_new = (e['K0']*q+X)*C-q*e['F']-z*(L+1-q)
identity = S.expand(t_new-q*t-(X-q*w)*C+z*(L+1-q*q))
require(identity==0,'transport elimination identity failed')
require(S.Poly(t_new,*variables).total_degree()==2,'new transport is not quadratic')

# A counterexample to cancellation q|XC => q|X, including the positive
# transport and L equations. This is NOT a solution of the full Pell system.
toy = {'beta':1,'J':3,'F':1,'alpha':1,'z':2,'K0':2,'X':6,'L':15}
require(q.subs({e[k]:v for k,v in toy.items()})==4,'toy q')
require(t_new.subs({e[k]:v for k,v in toy.items()})==0,'toy transport')
require(6%4!=0 and (6*2)%4==0,'toy cancellation')

summary = dict(status='PASS',repository_pin=PIN,
    scope='Exact symbolic algebra, direct substitution enumeration, and bounded proof obligations only; no new Con(ZFC) equation is certified.',
    parent_variables=31,parent_equations=22,parent_sos_degree=4,
    direct_monic_substitutions=len(records),direct_quartic_preserving_substitutions=0,
    direct_substitutions=records,
    rational_transport_identity=True,
    rational_transport_missing_obligation='Recover q|X (or establish gcd(C,q)=1) for every candidate zero. The new transport only gives q|XC.',
    cancellation_counterexample=dict(q=4,C=2,X=6,F=1,alpha=1,z=2,K0=2,L=15,
                                    scope='Transport and square-register equations only, not a complete source-system zero.'))
save('ELIMINATION_AUDIT.json',summary)

tree = json.loads((ROOT/'source_tree_records.json').read_text())
pins = []
for path in sorted((ROOT/'sources').iterdir()):
    data=path.read_bytes()
    record=tree[path.name]
    digest=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    require(digest==record['git_blob_sha1'],f'wrong upstream bytes: {path.name}')
    pins.append(dict(file=str(path.relative_to(ROOT)),repository_path=record['repository_path'],
                     git_blob_sha1=digest,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
save('SOURCE_PINS.json',dict(repository='VladimirReshetnikov/ProveIt',commit=PIN,files=pins))
print(json.dumps({k:v for k,v in summary.items() if k!='direct_substitutions'},indent=2))
