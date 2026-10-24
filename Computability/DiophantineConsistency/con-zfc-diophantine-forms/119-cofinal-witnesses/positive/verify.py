#!/usr/bin/env python3
"""Independent finite checks; no finite search is called a semantic proof."""
from collections import Counter
from copy import deepcopy
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import random
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
CASES = {
    'uncentered': ('saturated_upper', 89, 288, -1, 10, 152, 30, 62, 10, 32),
    'upper': ('saturated_upper', 91, 283, 1, 11, 149, 29, 61, 10, 32),
    'sharp': ('saturated_sharp', 92, 278, 1, 10, 146, 28, 60, 10, 32),
    'direct_uncentered': ('direct_saturated_upper', 94, 262, -1, 10, 126, 30, 62, 10, 32),
    'direct_upper': ('direct_saturated_upper', 96, 258, 1, 11, 124, 29, 61, 10, 32),
    'direct_sharp': ('direct_saturated_sharp', 97, 254, 1, 10, 122, 28, 60, 10, 32),
}

def require(condition, message):
    if not condition:
        raise ValueError(message)

def read(path):
    return json.loads(path.read_text())

def module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result

def pinned_sources():
    pins = read(ROOT/'SOURCE_PINS.json')
    n = 0
    for name, expected in pins.items():
        if name.startswith(('provenance/', 'parents/')):
            require(hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == expected,
                    'Frozen source changed: ' + name)
            n += 1
    return n

def check_graph(data, name):
    parent_name, operations, degree, *_ = CASES[name]
    require(data['operations'] == operations and data['exact_degree'] == degree,
            'Claimed metrics differ: ' + name)
    old = read(ROOT/'parents'/f'{parent_name}.json')
    old_map = {row[0]: row for row in old['source']}
    new_map = {row[0]: row for row in data['source']}
    require(len(new_map) == len(data['source']) == operations, 'Unique rows/count')
    deleted = {'L'} | ({'q4'} if name.startswith('direct_') else set())
    if 'uncentered' in name:
        deleted |= {'Cg', 'nVCg'}
    require(set(old_map)-set(new_map) == deleted and not set(new_map)-set(old_map),
            'Exact row deletions')
    for register, row in new_map.items():
        prior = list(old_map[register])
        if register == 'P1' and name.startswith('direct_'):
            require(row == ['P1', '*', 'q3', 'qbJ'], 'Direct shared product')
        else:
            for pos in [2, 3]:
                if prior[pos] == 'L': prior[pos] = 'cTR'
                if 'uncentered' in name and prior[pos] == 'nVCg': prior[pos] = 'nV'
            require(row == prior, 'Unchanged or exact declared row: ' + register)
    require(data['witnesses'] == old['witnesses'], 'All ten input names/order')
    require(data['fixed_numerals'] == old['fixed_numerals'] and
            data['coefficient_binding'] == old['coefficient_binding'], 'Whole coefficient binding')
    known = set(data['witnesses'] + data['fixed_numerals'])
    deps = {}
    for r, op, a, b in data['source']:
        require(r not in known and op in ['+', '-', '*'], 'Topological unique operation')
        require(all(type(x) is int or x in known for x in [a, b]), 'Defined operands')
        known.add(r); deps[r] = [a, b]
    live = set(); todo = [data['output']]
    while todo:
        x = todo.pop()
        if type(x) is not str or x in live: continue
        live.add(x); todo.extend(deps.get(x, []))
    require(known == live, 'Every input, port and gate is live')
    require(dict(Counter(r[1] for r in data['source'])) == data['operation_breakdown'],
            'Complete operation breakdown')
    return dict(Counter(r[1] for r in data['source']))

def evaluate(data, inp, modulus=None):
    values = dict(inp)
    for r, op, a, b in data['source']:
        a = values[a] if isinstance(a, str) else a
        b = values[b] if isinstance(b, str) else b
        v = a+b if op == '+' else a-b if op == '-' else a*b
        values[r] = v if modulus is None else v % modulus
    return values[data['output']]

def reference(inp, name):
    # Independently transcribed, unexpanded transport rather than graph center.
    J,F,alpha,i,T,Y,n,eta,zeta = [inp[x] for x in ['J','F','alpha','i','T','Y','n','eta','zeta']]
    beta,K,MC,MF = [inp[x] for x in ['beta','K0','MC','MF']]
    direct = name.startswith('direct_')
    q = beta*J+1; X = q+inp['x'] if direct else inp['w']*q
    mu = q*q+1; A = mu*Y*(X+1)+1; H = 4*A-5; Delta = A*A-1
    k = eta+zeta; c = k*Y+eta; U = i*c*c
    V0 = X*mu*mu*Y*Y; E = V0*(V0+1)*k*k+1
    Df = 1+Delta*U*U*E; Q = Delta*Delta*U*U*E; delta = Q-1
    R = ((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J; e = k-R-1
    b = c*(T+alpha)-R; V = Df*b-c; Dnum = Q*V*V-1
    C = q-F-alpha
    B = (q*K+X)*C-q*F if direct else (K+inp['w'])*C-F
    h = q*(q-1) if direct else q-1; P = q**3*h
    W = 1+h*b; M = P*mu*mu*H; Kpos = X*(3*c-2*X)+2
    center = 0 if 'uncentered' in name else (A if 'sharp' in name else A+1)*U*E
    Dlow = (q-1)*X if direct else 0
    Z = P*mu*mu*(H*(n+V+center)+Kpos) + H*(mu*mu*(h*Y-q**3*W*B-Dlow)-P*e)
    return (delta*Z*Z - M*M*(delta*E*Df+Dnum))**2 - 4*delta*M**4*E*Df*Dnum

def p_add(a, b, sign=1):
    out = dict(a)
    for powers, value in b.items():
        out[powers] = out.get(powers, 0) + sign*value
        if not out[powers]: del out[powers]
    return out

def p_mul(a, b):
    out = {}
    for e, x in a.items():
        for f, y in b.items():
            ef = tuple(i+j for i,j in zip(e, f))
            out[ef] = out.get(ef, 0)+x*y
    return {e:x for e,x in out.items() if x}

def p_scale(a, scalar):
    return {e:scalar*x for e,x in a.items() if scalar*x}

def universal_identities():
    z,g,y = [{tuple(int(i==j) for i in range(3)):1} for j in range(3)]
    one = {(0,0,0):1}
    norm = one
    for sg,sy in product([-1,1], repeat=2):
        norm = p_mul(norm,p_add(p_add(z,p_scale(g,sg)),p_scale(y,sy)))
    zg = p_add(p_add(p_mul(z,z),p_mul(g,g),-1),p_mul(y,y),-1)
    direct = p_add(p_mul(zg,zg),p_scale(p_mul(p_mul(g,g),p_mul(y,y)),4),-1)
    require(norm == direct, 'Every coefficient of four-factor norm')
    # Carrier replacement is a polynomial shear, with n_new=n_old+(b-L_old)B.
    n,b,L,B,h = [{tuple(int(i==j) for i in range(5)):1} for j in range(5)]
    one5 = {(0,0,0,0,0):1}
    newn = p_add(n,p_mul(p_add(b,L,-1),B))
    lhs = p_add(p_mul(h,newn),p_mul(p_add(one5,p_mul(h,b)),B),-1)
    rhs = p_add(p_mul(h,n),p_mul(p_add(one5,p_mul(h,L)),B),-1)
    require(lhs == rhs, 'Exact cleared carrier shear identity')
    return {'norm_collected_terms':len(norm),'universal_carrier_shear':True}

def trim(poly):
    while len(poly)>1 and poly[-1] == 0: poly.pop()
    return poly

def u_add(a,b,sign=1):
    n=max(len(a),len(b)); out=[0]*n
    for j,x in enumerate(a): out[j]+=x
    for j,x in enumerate(b): out[j]+=sign*x
    return trim(out)

def u_mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        if x:
            for k,y in enumerate(b):
                if y: out[j+k]+=x*y
    return trim(out)

def exact_degree_ray(data,name):
    ports={'beta':2,'K0':3,'MC':5,'MF':7}
    values={v:[0,1] for v in data['witnesses']} | {k:[v] for k,v in ports.items()}
    for r,op,a,b in data['source']:
        a=values[a] if isinstance(a,str) else [a]; b=values[b] if isinstance(b,str) else [b]
        values[r]=u_add(a,b) if op=='+' else u_add(a,b,-1) if op=='-' else u_mul(a,b)
    actual=values[data['output']]
    _,_,degree,sign,two,qexp,xexp,yexp,iexp,kexp=CASES[name]
    # On this exact ray q0=2t, k0=2t, w=t; direct x0=3t, q0-F=t.
    expected=sign*2**(two+qexp+kexp)*(3**xexp if name.startswith('direct_') else 1)
    require(len(actual)-1 == degree and actual[-1] == expected,
            'Exact Z[t] degree and top coefficient: '+name)
    require(qexp+xexp+yexp+iexp+kexp+2 == degree, 'Global homogeneous degree sum')
    return {'degree':degree,'leading_coefficient':str(expected),'finite_specialization_only':True}

def controls(data,name,ports):
    rng=random.Random(0x20261024+sum(map(ord,name)))
    for j in range(24):
        inp={v:rng.randint(-3,4) for v in data['witnesses']}
        inp|={'beta':rng.randint(-2,5),'K0':rng.randint(-2,5),'MC':rng.randint(-2,5),'MF':rng.randint(-2,5)}
        require(evaluate(data,inp)==reference(inp,name),'Exact signed full-polynomial control')
    for j in range(24):
        prime=[1000000007,1000000009,998244353][j%3]
        inp={v:rng.randint(-9,11) for v in data['witnesses']} | {k:v%prime for k,v in ports.items()}
        require(evaluate(data,inp,prime)==reference(inp,name)%prime,'Actual tuple modular control')
    return {'exact_signed_controls':24,'actual_port_modular_controls':24}

def mutation_controls(data,name):
    bad=[]
    a=deepcopy(data); a['exact_degree']+=1; bad.append(a)
    a=deepcopy(data); a['source'][0][2]='MC'; bad.append(a)
    a=deepcopy(data)
    row=next(r for r in a['source'] if r[0]=='LBt'); row[2]='k'; bad.append(a)
    a=deepcopy(data); a['source'].append(['dead','+',1,1]); bad.append(a)
    a=deepcopy(data); a['coefficient_binding']={'wrong_tuple':True}; bad.append(a)
    for obj in bad:
        failed=False
        try: check_graph(obj,name)
        except ValueError: failed=True
        require(failed,'Actual circuit corruption must be rejected')
    return len(bad)

def main():
    recipe=module(ROOT/'coefficients'/'recipe_compact44.py','recipe')
    coefficient_receipt=recipe.verify(); ports=recipe.recipe()
    frozen=pinned_sources(); identities=universal_identities()
    results=[]
    for name in CASES:
        d=read(ROOT/'equations'/f'{name}.json')
        results.append({'name':name,'operations':d['operations'],
                        'operation_breakdown':check_graph(d,name),
                        'controls':controls(d,name,ports),
                        'exact_degree_ray':exact_degree_ray(d,name),
                        'rejected_corruptions':mutation_controls(d,name)})
    print(json.dumps({'status':'PASS','optimized_python':bool(sys.flags.optimize),
                     'frozen_sources_checked':frozen,'coefficient_reconstruction':coefficient_receipt,
                     'universal_identities':identities,'equations':results,
                     'scope':'Finite specification checks only. PROOF.md gives the unbounded equivalence and global exact-degree proof.'},indent=2))

if __name__=='__main__': main()
