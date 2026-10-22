#!/usr/bin/env python3
"""Reproducible ordinary-strong refinement of the pinned blank67 circuit.

This verifies a circuit and local algebra. It does not certify the compiler,
decide Con(ZFC), or generate a full accepting K215 Pell witness.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parents[1]
PARENT_SHA256 = 'ceb76c8a0f5210645ac9cf9cf43bc662ba4052765416d8084ed6669831e5e59c'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def evaluate(source, values):
    v = dict(values)
    def arg(x):
        return x if isinstance(x, int) else v[x]
    for n, op, a, b in source:
        x, y = arg(a), arg(b)
        v[n] = x+y if op == '+' else x-y if op == '-' else x*y
    return v


def ledger(source):
    c = Counter(r[1] for r in source)
    return {'M': c['*'], 'A': c['+']+c['-'], 'operations': len(source)}


def build(parent):
    source = []
    for row in parent['source']:
        name = row[0]
        if name == 'aux_coefficient_root':
            source.append([name, '*', 'i', 'c2'])
        elif name == 'scaled_f_square':
            source.extend([
                ['f_square_minus_one', '-', 'L16', 1],
                ['ordinary_aux_coefficient', '*', 'A', 'f_square_minus_one'],
            ])
        elif name == 'norm_strong':
            source.extend([
                ['ordinary_strong_difference', '-', 'R16', 'ordinary_aux_coefficient'],
                [name, '+', 'ordinary_strong_difference', 1],
            ])
        elif name == 'L17':
            source.append([name, '*', 'ordinary_aux_coefficient', 'aux_square_gap'])
        elif name == 'polynomial':
            source.append([name, '-', 'seven_units', 1])
        else:
            source.append(row[:])
    p = {
        'name': 'ordinary_start_poly69',
        'witness_domain': 'strictly positive integers',
        'witnesses': parent['witnesses'],
        'fixed_numerals': parent['fixed_numerals'],
        'source': source,
        'output': 'polynomial',
        'ledger': ledger(source),
        'exact_degree': 99,
        'factor_exact_degrees': [22, 18, 28, 7, 2, 22],
        'factors': parent['factors'],
        'coefficient_recipe': 'Use all four ports together from data/four_cell_constants.json (new primary recipe), or all four from pinned 06-blank67 as a legacy alternative. The arithmetic theorem holds on either valid Start-only slice. Never mix ports.',
        'leading_form': '8*Q^55*h*gamma*i^2*(eta+zeta)^9*w^7*s^16*auxiliary_quotient^2*f^4*(w*(Q-F-alpha)-transport_quotient*Q), Q=Bm1*Jrep',
        'scope': 'Algebraic refinement with an ordinary proof; no Lean/Rocq formalization.',
    }
    finalizers = {'norm_pair', 'norm_four', 'norm_product', 'all_units',
                  'seven_units', 'polynomial', 'ordinary_strong_difference',
                  'norm_strong'}
    sys_source = [r for r in source if r[0] not in finalizers]
    comparisons = [[n, 1] for n in parent['factors'][:-1]]
    comparisons.append(['R16', 'ordinary_aux_coefficient'])
    system = {**p, 'name': 'ordinary_start_system61', 'source': sys_source,
              'comparisons': comparisons, 'ledger': ledger(sys_source),
              'residual_exact_degrees': [22, 18, 28, 7, 2, 22],
              'maximum_residual_degree': 28}
    system.pop('output')
    system.pop('exact_degree')
    system.pop('factors')
    system.pop('factor_exact_degrees')
    system.pop('leading_form')
    sos_source = copy.deepcopy(sys_source)
    squares = []
    for j, (a,b) in enumerate(comparisons):
        r, s = f'residual{j}', f'residual_square{j}'
        sos_source.extend([[r, '-', a,b], [s, '*',r,r]])
        squares.append(s)
    acc = squares[0]
    for j, s in enumerate(squares[1:]):
        n = f'sum{j}'
        sos_source.append([n, '+', acc, s])
        acc=n
    sos = {**p, 'name': 'ordinary_start_sos78', 'source': sos_source,
           'output': acc, 'ledger': ledger(sos_source), 'exact_degree':56,
           'leading_form': '(eta+zeta)^4*w^4*s^8*Q^28*auxiliary_quotient^4*f^8, Q=Bm1*Jrep'}
    sos.pop('factors')
    sos.pop('factor_exact_degrees')
    return p, system, sos


def check_dag(packet):
    known = set(packet['witnesses']+packet['fixed_numerals'])
    producers = {}
    for row in packet['source']:
        n,op,a,b=row
        require(n not in known, 'duplicate gate')
        require(op in '+-*', 'unknown operation')
        require(all(isinstance(x,int) or x in known for x in (a,b)), 'unknown operand')
        known.add(n)
        producers[n]=row
    live=set()
    def visit(n):
        if isinstance(n,int) or n in live: return
        live.add(n)
        if n in producers:
            visit(producers[n][2]);visit(producers[n][3])
    if 'comparisons' in packet:
        for pair in packet['comparisons']:
            for n in pair:visit(n)
    else:visit(packet['output'])
    require(set(producers)<=live, 'dead gate')
    require(set(packet['witnesses']+packet['fixed_numerals'])<=live, 'dead port')


def formula(vals):
    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma = [vals[n] for n in
        ['Jrep','F','alpha','transport_quotient','f','h','i','auxiliary_quotient',
         's','w','tau_root','eta','zeta','y_aux','gamma']]
    q=vals['Bm1']*J+1; C=q-F-alpha
    X=w*q;Y=s*q**3;E=X*Y;k=eta+zeta;c=k*Y+eta;a=E+Y
    H=4*a+3;Delta=a*a+H;D=X+a*c+gamma*H
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(vals['MC']+q*vals['MF'])*J
    L=E*k*Y
    V=c*(T*f-1)-R*f*f
    K=Delta*(f*f-1)
    factors=[tau*tau-L*(L+k),D*D-Delta*c*c,K*(V*V-y*y)+y*y,
             k-h*E-R,(vals['Kconstant']+w)*C+(q-F)-z*(q-1),
             1+(i*c*c)**2-K]
    p=1
    for a in factors:p*=a
    return p-1,factors


def univar_degrees(packet, seed):
    # Exact polynomial arithmetic modulo a prime; an attained degree is a
    # lower bound. The uniform leading-form proof supplies the upper bound.
    prime=1000003
    rng=random.Random(seed)
    def poly(x):return [x%prime] if isinstance(x,int) else values[x]
    def add(a,b,sign=1):
        c=[0]*max(len(a),len(b))
        for j,x in enumerate(a):c[j]=(c[j]+x)%prime
        for j,x in enumerate(b):c[j]=(c[j]+sign*x)%prime
        while len(c)>1 and c[-1]==0:c.pop()
        return c
    def mul(a,b):
        c=[0]*(len(a)+len(b)-1)
        for j,x in enumerate(a):
            for k,y in enumerate(b):c[j+k]=(c[j+k]+x*y)%prime
        while len(c)>1 and c[-1]==0:c.pop()
        return c
    values={n:[rng.randrange(1,30),rng.randrange(1,30)] for n in packet['witnesses']}
    values.update({n:[rng.randrange(1,30)] for n in packet['fixed_numerals']})
    for n,op,a,b in packet['source']:
        a,b=poly(a),poly(b)
        values[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
    if 'comparisons' in packet:
        return [len(add(poly(a),poly(b),-1))-1 for a,b in packet['comparisons']]
    return len(values[packet['output']])-1


def checks(packets):
    p,system,sos=packets
    for packet in packets:check_dag(packet)
    require(p['ledger']=={'M':39,'A':30,'operations':69}, 'product ledger')
    require(system['ledger']=={'M':34,'A':27,'operations':61}, 'system ledger')
    require(sos['ledger']=={'M':40,'A':38,'operations':78}, 'SOS ledger')
    cases=0
    for seed in range(200):
        rng=random.Random(seed)
        vals={n:rng.randrange(-5,7) for n in p['witnesses']+p['fixed_numerals']}
        ev=evaluate(p['source'],vals)
        fp,ff=formula(vals)
        require(ev[p['output']]==fp, 'independent formula')
        require([ev[n] for n in p['factors']]==ff, 'independent factors')
        evs=evaluate(sos['source'],vals)
        require(evs[sos['output']]==sum((x-1)**2 for x in ff), 'sum of squares')
        cases+=1
    for a in range(4):
        d=(a+2)**2-1
        for i in range(4):
            for c in range(4):
                for f in range(4):
                    require((1+(i*c*c)**2-d*(f*f-1))%4!=3, 'negative strong unit')
    degrees={}
    for packet in packets:
        ds=[univar_degrees(packet,seed) for seed in (31,57,103)]
        exp=packet.get('residual_exact_degrees') if 'comparisons' in packet else packet['exact_degree']
        require(all(d==exp for d in ds), 'degree diagnostic: '+packet['name'])
        degrees[packet['name']]=ds
    return {'status':'PASS','random_signed_formula_cases':cases,
            'all_dags_live':True,'strong_negative_unit_residue_cases':256,
            'degree_diagnostics':degrees,
            'scope':'Finite local algebra and circuit diagnostics; not a proof of the compiler or existence/nonexistence of a K215 accepting tuple.'}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--parent',type=Path,default=ROOT/'vendor/fixed_blank_67.json')
    ap.add_argument('--out',type=Path,default=ROOT/'data')
    ap.add_argument('--write',action='store_true',help='Regenerate packets; default is read-only verification.')
    args=ap.parse_args()
    raw=args.parent.read_bytes()
    require(hashlib.sha256(raw).hexdigest()==PARENT_SHA256, 'pinned parent hash mismatch')
    doc=json.loads(raw)
    packets=build(doc.get('packet',doc))
    receipt=checks(packets)
    results=[(p['name']+'.json',p) for p in packets]
    results.append(('ordinary_start_checks.json',receipt))
    if args.write:
        args.out.mkdir(parents=True,exist_ok=True)
        for name,result in results:
            (args.out/name).write_text(json.dumps(result,indent=2)+'\n')
    else:
        for name,result in results:
            require(json.loads((args.out/name).read_text())==result, 'saved packet mismatch: '+name)
    print(json.dumps({'receipt':receipt,'ledgers':{p['name']:p['ledger'] for p in packets}},indent=2))


if __name__=='__main__':main()
