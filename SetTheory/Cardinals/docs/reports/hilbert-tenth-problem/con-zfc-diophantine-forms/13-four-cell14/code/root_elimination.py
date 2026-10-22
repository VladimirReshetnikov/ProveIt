#!/usr/bin/env python3
"""Build and audit the two 14-variable circuits, using the standard library.

Arithmetic identities and finite diagnostics are checked here. This program
does not certify the Pell/compiler theorems, ZFC consistency, or a K215 run.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
import argparse
import hashlib
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parents[1]
COMMIT = '3b201cdea32d2c816f5f3d20734051f25fd3ef14'
PARENT_SHA256 = 'ceb76c8a0f5210645ac9cf9cf43bc662ba4052765416d8084ed6669831e5e59c'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def evaluate(rows, values):
    env = dict(values)
    get = lambda x: x if isinstance(x, (int, Fraction)) else env[x]
    for name, op, left, right in rows:
        a, b = get(left), get(right)
        env[name] = a+b if op == '+' else a-b if op == '-' else a*b
    return env


def audit_graph(rows, ports, output):
    known, counts = set(ports), Counter()
    for name, op, a, b in rows:
        require(name not in known and op in '+-*', 'invalid gate')
        for v in (a, b):
            require(type(v) is int or v in known, 'unknown operand: '+str(v))
        known.add(name)
        counts['M' if op == '*' else 'A'] += 1
    needed = {output}
    for name, op, a, b in reversed(rows):
        if name in needed:
            needed.update(v for v in (a, b) if isinstance(v, str))
    require(all(r[0] in needed for r in rows), 'dead gate')
    require(set(ports) <= needed, 'dead port')
    return dict(operations=len(rows), multiplications=counts['M'],
                additions_subtractions=counts['A'], all_gates_live=True,
                all_ports_live=True)


NORM_TAIL = [
 ['r_ic2','*','i','c2'], ['r_Dminus','*','r_ic2','aux_coefficient_root'],
 ['r_D','+','r_Dminus',1], ['r_RD','*','r_lhs','r_D'],
 ['r_b','+','R10a','r_RD'], ['r_u','*','R10a','auxiliary_quotient'],
 ['r_u2','*','r_u','r_u'], ['r_p','*','r_D','r_u2'],
 ['r_b2','*','r_b','r_b'], ['r_Pa','*','norm_pair','norm_index'],
 ['r_P','*','r_Pa','norm_transport'], ['r_sum','+','r_p','r_b2'],
 ['r_gap','-','r_sum','aux_y2'], ['r_Qgap','*','R16','r_gap'],
 ['r_Aplus','+','r_Qgap','aux_y2'], ['r_A','-','r_Aplus',1],
 ['r_Qp','*','R16','r_p'], ['r_Qb2','*','R16','r_b2'],
 ['r_cross','*','r_Qp','r_Qb2'], ['r_four','*',4,'r_cross'],
 ['r_A2','*','r_A','r_A'], ['r_norm','-','r_A2','r_four'],
 ['r_unit','+','r_norm',1], ['r_product','*','r_P','r_unit'],
 ['polynomial14','-','r_product',1]]

OUTER_TAIL = NORM_TAIL[:11] + [
 ['o_C','*','r_P','R16'], ['o_L','*','o_C','r_p'],
 ['o_M','*','o_C','r_b2'], ['o_Pc','-','r_P','o_C'],
 ['o_Z','*','o_Pc','aux_y2'], ['o_LM','+','o_L','o_M'],
 ['o_LMZ','+','o_LM','o_Z'], ['o_alpha','-','o_LMZ',1],
 ['o_alpha2','*','o_alpha','o_alpha'], ['o_prod','*','o_L','o_M'],
 ['o_four','*',4,'o_prod'], ['polynomial14','-','o_alpha2','o_four']]


def degree_bounds(rows, witnesses, constants):
    degree = dict.fromkeys(witnesses, 1) | dict.fromkeys(constants, 0)
    for name, op, a, b in rows:
        da, db = (0 if type(v) is int else degree[v] for v in (a,b))
        degree[name] = da+db if op == '*' else max(da,db)
        if name == 'norm_main':
            # Exact identity printed in the article, not a zero-set rewrite.
            degree[name] = max(2*degree['wn2'], degree['wn2']+degree['gam'],
                               2*degree['gam'], degree['R12']+degree['R10a']+degree['wn2'],
                               degree['R12']+degree['R10a']+degree['gam'],
                               degree['a4m5']+2*degree['R10a'])
    return degree


def line_degrees(rows, witnesses, constants, targets, prime=1000000007):
    """Evaluate entire circuits in F_prime[t]; diagnostic only."""
    env = {w: [2*j+1, 3*j+2] for j,w in enumerate(witnesses)}
    env.update({c:[v] for c,v in zip(constants,[15,37,2,19])})
    def get(v): return [v%prime] if type(v) is int else env[v]
    for name, op, a, b in rows:
        a,b = get(a),get(b)
        if op == '*':
            value=[0]*(len(a)+len(b)-1)
            for i,x in enumerate(a):
                for j,y in enumerate(b): value[i+j]=(value[i+j]+x*y)%prime
        else:
            value=[0]*max(len(a),len(b))
            for j,x in enumerate(a):value[j]=x
            for j,y in enumerate(b):value[j]=(value[j]+(y if op=='+' else -y))%prime
        while len(value)>1 and value[-1]==0:value.pop()
        env[name]=value
    return {name:dict(degree=len(env[name])-1, leading_coefficient=env[name][-1])
            for name in targets}


# A tiny sparse polynomial implementation for exact all-ring identities.
class Poly:
    def __init__(self, terms):
        self.t={m:c for m,c in terms.items() if c}
    @staticmethod
    def c(n):return Poly({(0,)*8:n})
    @staticmethod
    def var(j):return Poly({tuple(int(i==j) for i in range(8)):1})
    def __add__(self, other):
        other=other if isinstance(other,Poly) else Poly.c(other)
        d=dict(self.t)
        for m,c in other.t.items():d[m]=d.get(m,0)+c
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.t.items()})
    def __sub__(self,o):return self+-o if isinstance(o,Poly) else self+(-o)
    def __rsub__(self,o):return -self+o
    def __mul__(self,o):
        o=o if isinstance(o,Poly) else Poly.c(o)
        d={}
        for a,x in self.t.items():
            for b,y in o.t.items():
                m=tuple(u+v for u,v in zip(a,b));d[m]=d.get(m,0)+x*y
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        a=Poly.c(1)
        for _ in range(n):a=a*self
        return a


def exact_identities():
    P,Q,D,u,b,y,f,R=[Poly.var(j) for j in range(8)]
    A=Q*(D*u*u+b*b-y*y)+y*y-1
    B=2*Q*u*b
    K=A*A-D*B*B
    phi=P*(K+1)-1
    psi=(P*(A+1)-1)**2-D*(P*B)**2
    require(not (psi-P*phi-(P-1)*(2*P*A-1)).t,'outer/local norm identity')
    # c is b-RD at this boundary.  The main auxiliary expression is
    # V=uf-c-Rf^2=uf-b-R(f^2-D).
    E=f*f-D
    V=u*f-b-R*E
    Na=Q*V*V-(Q-1)*y*y
    correction=Q*(u*u-2*R*u*f+2*R*b+R*R*E)
    require(not (Na-1-A+B*f-E*correction).t,'auxiliary reduction identity')
    require(not (D*B*B-4*(Q*D*u*u)*(Q*b*b)).t,'factored norm cross term')
    return ['outer/local norm polynomial identity', 'auxiliary reduction modulo f^2-D',
            'factored norm cross term']


def build(parent):
    dependent={'f'};retained=[]
    for row in parent['source']:
        if any(isinstance(v,str) and v in dependent for v in row[2:]):dependent.add(row[0])
        else:retained.append(row)
    require(len(retained)==50,'50 retained producers')
    witnesses=[w for w in parent['witnesses'] if w!='f']
    constants=parent['fixed_numerals']
    packets={}
    for name,tail,expected,degree in [('root14_product75',NORM_TAIL,75,293),
                                     ('root14_outer73',OUTER_TAIL,73,342)]:
        rows=retained+tail
        ledger=audit_graph(rows,witnesses+constants,'polynomial14')
        require(ledger['operations']==expected,'operation total')
        bounds=degree_bounds(rows,witnesses,constants)
        require(bounds['polynomial14']==degree,'degree upper bound')
        diagnostic=line_degrees(rows,witnesses,constants,['polynomial14'])
        require(diagnostic['polynomial14']['degree']==degree,'line degree')
        packets[name]=dict(name=name,source_commit=COMMIT,witnesses=witnesses,
            witness_domain='strictly positive integers',fixed_numerals=constants,
            source=rows,output='polynomial14',ledger=ledger,exact_degree=degree,
            degree_bounds=bounds,line_degree_diagnostic=diagnostic,
            proof='report.tex: signed quotient lemma and root elimination theorem',
            coefficient_recipe='All four ports from data/four_cell_constants.json; the four ports from pinned package 06 are a separate legacy alternative. Do not mix the two recipes.',
            caveat='Finite diagnostics do not verify the semantic compiler theorem.')
    for old_name in list(packets):
        old=packets[old_name]
        prefix=[];ports=[]
        for name in old['witnesses']:
            if name in ('tau_root','y_aux'):
                ports.append(name)
                continue
            u,v,t=[name+'_'+suffix for suffix in ('pos_u','pos_v','pos_t')]
            ports.extend([u,v,t])
            prefix.extend([
                [name+'_u2','*',u,u], [name+'_v2','*',v,v],
                [name+'_t1','+',t,1], [name+'_tri','*',t,name+'_t1'],
                [name+'_uv','+',name+'_u2',name+'_v2'],
                [name+'_sum','+',name+'_uv',name+'_tri'],
                [name,'+',name+'_sum',1]])
        rows=prefix+old['source']
        ledger=audit_graph(rows,ports+constants,'polynomial14')
        require(len(ports)==38 and len(prefix)==84,'integer substitution dimensions')
        diagnostic=line_degrees(rows,ports,constants,['polynomial14'])
        require(diagnostic['polynomial14']['degree']==2*old['exact_degree'],'integer degree')
        name=old_name+'_integer38'
        packets[name]={**old,'name':name,'source':rows,'witnesses':ports,
            'witness_domain':'all integers','ledger':ledger,
            'exact_degree':2*old['exact_degree'],
            'degree_bounds':degree_bounds(rows,ports,constants),
            'line_degree_diagnostic':diagnostic,
            'proof':'report.tex: integer conversion; tau and y occur only squared and cannot vanish at zeros.'}
    return packets


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    parent_path=ROOT/'vendor'/'fixed_blank_67.json'
    require(hashlib.sha256(parent_path.read_bytes()).hexdigest()==PARENT_SHA256,'pinned parent hash')
    parent=json.loads(parent_path.read_text())['packet']
    packets=build(parent)
    identities=exact_identities()
    rng=random.Random(21514);trials=64
    for _ in range(trials):
        values={w:Fraction(rng.randint(-5,7),rng.randint(1,3)) for w in parent['witnesses']}
        values.update(dict(Bm1=15,Kconstant=37,MC=2,MF=19))
        a=evaluate(packets['root14_product75']['source'],values)
        b=evaluate(packets['root14_outer73']['source'],values)
        P,Q,D,u,z,y2=[a[k] for k in ['r_P','R16','r_D','r_u','r_b','aux_y2']]
        aa=Q*(D*u*u+z*z-y2)+y2-1
        bb=2*Q*u*z
        require(a['polynomial14']==P*(aa*aa-D*bb*bb+1)-1,'local formula')
        require(b['polynomial14']==(P*(aa+1)-1)**2-D*(P*bb)**2,'outer formula')
    receipt=dict(status='PASS',identities=identities,exact_rational_trials=trials,
                 parent_sha256=hashlib.sha256(parent_path.read_bytes()).hexdigest(),
                 circuits={n:dict(variables=len(p['witnesses']),degree=p['exact_degree'],**p['ledger'])
                           for n,p in packets.items()},
                 limits='Not a kernel check, not a K215 halting test, not a materialization of coefficients.')
    for name,packet in packets.items():
        path=ROOT/'data'/(name+'.json')
        if args.write:path.write_text(json.dumps(packet,indent=2)+'\n')
        else:require(json.loads(path.read_text())==packet,'packet mismatch: '+name)
    path=ROOT/'data'/'root_elimination_checks.json'
    if args.write:path.write_text(json.dumps(receipt,indent=2)+'\n')
    else:require(json.loads(path.read_text())==receipt,'receipt mismatch')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
