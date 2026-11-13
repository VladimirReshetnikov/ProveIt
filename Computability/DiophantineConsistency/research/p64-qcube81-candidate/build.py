#!/usr/bin/env python3
"""Construct and verify the unproved P64 q-cube quotient candidate.

The comparisons are exact algebra or finite checks, not a Lean proof of
zero-existence equivalence. Default mode checks retained generated files;
--write creates them only if neither exists.
"""
import hashlib
import json
import random
import runpy
import sys
from collections import Counter
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PARENT = ROOT / 'Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/positive14/polynomial.json'
VERIFY = PARENT.with_name('verify.py')
VERIFY_SHA = '97de6a4ff04997de2c5e0062c4c8b335cf4c8da6b1cd2b85b543948a62e3677b'
if hashlib.sha256(VERIFY.read_bytes()).hexdigest() != VERIFY_SHA:
    raise RuntimeError('parent verifier hash drift')
PARENT_SHA = 'b9731360a30bcbcfd6f9161241cafb01b8c5d68aa40b84ddc50ba689a0745d0e'
raw = PARENT.read_bytes()
if hashlib.sha256(raw).hexdigest() != PARENT_SHA:
    raise RuntimeError('parent graph hash drift')
parent = json.loads(raw)
if len(parent['source']) != 83 or parent['witnesses'][7] != 'Y':
    raise RuntimeError('unexpected parent structure')

removed = {'ell_plus_rho', 'scaled_gap', 'first_carrier', 'first_carrier_square',
           'q6', 'scaled_first_radicand', 'A0'}
rows = []
for row in parent['source']:
    name = row[0]
    if name in removed:
        if name == 'A0':
            rows += [['ell_plus_rho','+','ell','rho'],
                     ['first_unscaled','+','ell_plus_rho','s'],
                     ['first_unscaled_square','*','first_unscaled','first_unscaled'],
                     ['A0','-','first_unscaled_square','first_radicand']]
        continue
    rows.append(row)
    if name == 'q3':
        rows.append(['Y','*','q3','s'])
inserted = {'Y', 'ell_plus_rho', 'first_unscaled', 'first_unscaled_square', 'A0'}
unchanged = [row for row in parent['source'] if row[0] not in removed]
if [row for row in rows if row[0] not in inserted] != unchanged:
    raise RuntimeError('unchanged parent gate structure differs')
witnesses = list(parent['witnesses'])
witnesses[7] = 's'
ports = parent['fixed_numerals']
known = set(witnesses + ports)
deps = {}
for name, op, x, y in rows:
    if name in known or op not in ('+','-','*') or any(not isinstance(v,int) and v not in known for v in (x,y)):
        raise RuntimeError('duplicate, invalid or non-topological gate: ' + str(name))
    known.add(name)
    deps[name] = [v for v in (x,y) if isinstance(v,str)]
seen, todo = set(), [parent['output']]
while todo:
    name = todo.pop()
    if name in seen:
        continue
    seen.add(name)
    todo.extend(deps.get(name, []))
if len(rows) != 81 or len(seen.intersection(deps)) != 81 or not set(witnesses + ports) <= seen:
    raise RuntimeError('unexpected count, dead gate, or unused input')
count = dict(Counter(row[1] for row in rows))

# Exact symbolic polynomial identity for the changed first residual.
classes = runpy.run_path(str(VERIFY))
Poly, Lead = classes['Poly'], classes['Lead']
if classes['identities']() != 4:
    raise RuntimeError('parent residual identities failed')
q,l,r,s,k = [Poly.var(n) for n in ('q','l','r','s','k')]
first_old = (q**3*(l+r)+q**3*s)**2-q**6*(l*(l+k)+1)
first_new = (l+r+s)**2-(l*(l+k)+1)
if first_old != q**6*first_new:
    raise RuntimeError('first residual identity failed')

# Exact leading-form certificate. The expanded forms avoid cancellations in
# the main carrier and the auxiliary norm, exactly as in the parent verifier.
v = {n: Lead.var(n) for n in witnesses}
v.update({n: Lead.var(n, 0) for n in ports})
J,F,alpha,z,f,i,T,s,w,rho,eta,zeta,e,gamma = [v[n] for n in witnesses]
beta,K0,MC,MF = [v[n] for n in ports]
q = beta*J+1; Y = q**3*s; X = w*q; E = X*Y; k = eta+zeta
c = k*Y+eta; a = E+Y; H = 4*a+3; Delta = a*a+H; ell = E*k*Y
R = ((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
r = k-R-1; U = Y*Y; I = i*c*c; Aaux = Delta*(f*f-1)
V = f*f*(c*T-R)-c
A0 = ell*(2*(rho+s)-k)+(rho+s)**2-1
D0 = X+a*c+H*gamma
D0gap = 2*a*c*(X+H*gamma)+(X+H*gamma)**2-H*c*c-1
M = U*U*D0gap-2*U*H*r*D0+H*H*r*r
W = I*I-Aaux
Na = V*V-(Aaux-1)*e*(2*V+e)
Lt = (K0+w)*(q-F-alpha)-F-z*(q-1)
output = A0*A0+M*M+W*W+Na*Na+Lt*Lt-1
expected = 64*Poly.var('beta')**46*Poly.var('J')**46*Poly.var('w')**4*Poly.var('s')**14*(Poly.var('eta')+Poly.var('zeta'))**2*Poly.var('gamma')**2
if output.degree != 68 or output.p != expected:
    raise RuntimeError('unexpected degree or leading form')

# Exact polynomial identities were checked above. These additional modular
# samples test the graph rewriting, including every unchanged residual.
def evaluate(graph_rows, initial, modulus):
    values = {key: value % modulus for key,value in initial.items()}
    def get(v): return v % modulus if isinstance(v,int) else values[v]
    for name,op,x,y in graph_rows:
        a,b = get(x),get(y)
        values[name] = {'+':lambda:(a+b)%modulus,
                        '-':lambda:(a-b)%modulus,
                        '*':lambda:(a*b)%modulus}[op]()
    return values

rng = random.Random(0x8168)
checks = 0
for modulus in (1000003,1000033,1000037):
    for _ in range(200):
        sample = {n:rng.randrange(1,modulus) for n in witnesses+ports}
        new = evaluate(rows,sample,modulus)
        old_input = {n:sample[n] for n in parent['witnesses'] if n!='Y'}
        old_input['Y'] = new['Y']
        old_input.update({n:sample[n] for n in ports})
        old = evaluate(parent['source'],old_input,modulus)
        q6 = pow(new['q'],6,modulus)
        if old['A0'] != q6*new['A0']%modulus:
            raise RuntimeError('first residual graph check failed')
        if any(old[n] != new[n] for n in ('M','W','Na','Lt')):
            raise RuntimeError('unchanged residual graph check failed')
        if (old['polynomial']-new['polynomial']-(q6*q6-1)*new['A0']**2)%modulus:
            raise RuntimeError('output scaling graph check failed')
        checks += 1

graph = {'name':'p64_qcube_positive14_degree68',
         'witness_domain':'strictly positive integers', 'witnesses':witnesses,
         'fixed_numerals':ports, 'source':rows, 'output':parent['output'],
         'operations':len(rows), 'operation_counts':count,
         'exact_degree':68, 'status':'candidate; zero-existence equivalence and iPRA endpoint unproved',
         'parent_graph_sha256':PARENT_SHA,
         'parent_binding':'Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/positive14/native/COEFFICIENT_BINDING.json'}
metrics = {'status':'PASS_FINITE_AND_SYMBOLIC_CHECKS_ONLY', 'parent_sha256':PARENT_SHA,
           'builder_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'operations':len(rows), 'operation_counts':count, 'live_gates':len(seen.intersection(deps)),
           'witnesses':len(witnesses), 'degree':68,
           'residual_degrees':{n:t.degree for n,t in [('A0',A0),('M',M),('W',W),('Na',Na),('Lt',Lt)]},
           'leading_form':'64*beta^46*J^46*w^4*s^14*(eta+zeta)^2*gamma^2',
           'leading_form_condition':'beta != 0', 'exact_first_factor_identity':True,
           'parent_residual_identities':4, 'unchanged_parent_rows':len(unchanged),
           'modular_graph_samples':checks,
           'scope':'Finite graph checks and exact symbolic algebra; no model-level or iPRA equivalence.'}
outputs = [(HERE/'graph.json',json.dumps(graph,indent=2)+'\n'),
           (HERE/'checks.json',json.dumps(metrics,indent=2,sort_keys=True)+'\n')]
if sys.argv[1:] == ['--write']:
    for path,_ in outputs:
        if path.exists(): raise SystemExit(f'refusing to overwrite {path}')
    for path,text in outputs: path.write_text(text)
elif sys.argv[1:]:
    raise SystemExit('usage: python3 -I -S -B build.py [--write]')
else:
    for path,text in outputs:
        if path.read_text()!=text: raise SystemExit(f'generated bytes differ: {path}')
print(json.dumps({k:metrics[k] for k in ('status','operations','operation_counts','degree','residual_degrees','modular_graph_samples')},sort_keys=True))
