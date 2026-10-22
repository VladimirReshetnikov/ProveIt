#!/usr/bin/env python3
"""Build and audit 27-integer amalgamations of ProveIt's normalized core.

This file checks finite algebra and arithmetic-circuit ledgers.  The semantic
theorem is in PROOF.md; no run or Pell witness of K215 is claimed.
Only Python's standard library is needed.  All checks survive python -O.
"""
from collections import Counter
from fractions import Fraction
from pathlib import Path
import json
import random

HERE = Path(__file__).resolve().parent
PIN = 'f0ae4e0991ca44a7bb4e5671d42e33d775e48035'
POSITIVE = ['Jrep','F','alpha','transport_quotient','s','eta','zeta']

def require(test, message):
    if not test:
        raise AssertionError(message)

def evaluate(source, values):
    env = dict(values)
    for name, op, a, b in source:
        av = a if isinstance(a, int) else env[a]
        bv = b if isinstance(b, int) else env[b]
        env[name] = av + bv if op == '+' else av - bv if op == '-' else av * bv
    return env

def build(lower):
    filename = 'polynomial13_lowweight85.json' if lower else 'polynomial13_84.json'
    original = json.loads((HERE/'upstream'/filename).read_text())
    prefix, witnesses = [], []
    for port in POSITIVE:
        xs = [port + '_' + suffix for suffix in ('a','b','c')]
        witnesses.extend(xs)
        a,b,c = xs
        prefix.extend([
            [port+'_a2','*',a,a], [port+'_aa','+',port+'_a2',a],
            [port+'_b2','*',b,b], [port+'_c2','*',c,c],
            [port+'_ab','+',port+'_aa',port+'_b2'],
            [port+'_abc','+',port+'_ab',port+'_c2'],
            [port,'+',port+'_abc',1]])
    witnesses.extend(['h','r','auxiliary_quotient','u','gamma','t'])
    prefix.extend([['twor','*',2,'r'],['i','+','twor',1],['w','*','u','u']])
    source = prefix + original['source']
    ops = 137 if lower else 136
    degree = 1004 if lower else 1116
    out = {
        'name':f'integer27_product{ops}', 'domain':'unrestricted integers',
        'witnesses':witnesses, 'fixed_numerals':original['fixed_numerals'],
        'source':source, 'output':'polynomial', 'exact_degree':degree,
        'coefficient_binding': {
            'repository':'VladimirReshetnikov/ProveIt','source_pin':PIN,
            'default_whole_tuple': '../COEFFICIENT_BINDINGS.json',
            'ports':['Bm1 = B - 1','Kconstant = D_C + B D_R','MC','MF = M_F_native + B - 1'],
            'scope':'T4 interface transfer uses its odd five-power padding. Never splice tuple entries.'},
        'proof':'PROOF.md',
        'weight':'k (i c^2)^2 + T^2' if lower else 'D + (cT)^2',
        'status':'New mathematical reduction; finite algebra checks only, not a Lean/Rocq formalization.'}
    audit_ledger(out, ops)
    system = json.loads(json.dumps(out))
    system['source'] = source[:-6]
    system.pop('output'); system.pop('exact_degree')
    system['name'] = f'integer27_system{ops-6}'
    system['comparisons']=[['norm_main',1],['norm_index',1],['norm_transport',1],['UU2','sixteenC2PU']]
    system['residual_exact_degrees']=[35,13,4,952 if lower else 1064]
    audit_ledger(system, ops-6)
    return out, system

def audit_ledger(packet, expected):
    source = packet['source']
    free = packet['witnesses'] + packet['fixed_numerals']
    known = set(free)
    for n,op,a,b in source:
        require(n not in known and op in ('+','-','*'), ('bad gate',n))
        require(all(isinstance(x,int) or x in known for x in (a,b)), ('unknown input',n))
        known.add(n)
    roots=[packet['output']] if 'output' in packet else [x for row in packet['comparisons'] for x in row if isinstance(x,str)]
    live = set(roots)
    for n,op,a,b in reversed(source):
        if n in live:
            live.update(x for x in (a,b) if isinstance(x,str))
    require(all(n in live for n,_,_,_ in source), 'dead gate')
    require(set(free) <= live, 'dead port')
    require(len(packet['witnesses']) == 27, 'variable count')
    require(len(source) == expected, 'operation count')
    counts=Counter(x[1] for x in source)
    packet['ledger']={'operations':len(source),'multiplications':counts['*'],
                      'additions_subtractions':counts['+']+counts['-'],
                      'all_gates_live':True,'all_ports_live':True}

def independent(values, lower):
    def pos(name):
        a,b,c=[values[name+'_'+s] for s in ('a','b','c')]
        return a*a+a+b*b+c*c+1
    J,F,alpha,z,s,eta,zeta=map(pos,POSITIVE)
    h,r,T,u,gamma,t=[values[x] for x in ('h','r','auxiliary_quotient','u','gamma','t')]
    beta,K,MC,MF=[values[x] for x in ('Bm1','Kconstant','MC','MF')]
    i=2*r+1; w=u*u; q=beta*J+1
    X=w*q; Y=s*q**3; E=X*Y; k=eta+zeta; c=k*Y+eta
    a=E+Y; H=4*a+3; delta=a*a+H; main=X+a*c+gamma*H
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    n1=main*main-delta*c*c; nk=k-h*E-R
    nt=(K+w)*(q-F-alpha)+q-F-z*(q-1)
    ell=E*k*Y; A=1+ell*(ell+k); I=i*c*c
    D=1+delta*I*I; Q=delta*(D-1); v=c*T; z0=c+R*D; d=Q-1
    M=k*I*I+T*T if lower else D+v*v
    e=Q*(D*v*v+z0*z0)-1; B=2*Q*v*z0
    C=d*(t*t+M*M*A)-e
    U=C*C+D*B*B-4*d*d*t*t*M*M*A
    res=U*U-D*(2*C*B)**2
    return [n1,nk,nt,res], n1*nk*nt*(1+res)-1

def formula_checks(p, lower):
    rng=random.Random(27137 if lower else 27136)
    for sample in range(96):
        values={x:rng.randrange(-2,4) for x in p['witnesses']+p['fixed_numerals']}
        got=evaluate(p['source'],values)
        truth, polynomial=independent(values,lower)
        require(got['polynomial']==polynomial,('independent formula',sample))
        require([got['norm_main'],got['norm_index'],got['norm_transport'],got['norm13']]==truth,('residuals',sample))
    return {'independent_signed_assignments':96,'includes_zero_u_T_t':True}

def polynomial_degree_check(packet, seed, prime):
    rng=random.Random(seed)
    env={v:[rng.randrange(1,11),rng.randrange(1,11)] for v in packet['witnesses']}
    env.update({v:[c] for v,c in zip(packet['fixed_numerals'],[31,127,10,45])})
    def plus(a,b,sign):
        ans=[((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))]
        while len(ans)>1 and ans[-1]==0: ans.pop()
        return ans
    for n,op,a,b in packet['source']:
        aa=[a] if isinstance(a,int) else env[a]
        bb=[b] if isinstance(b,int) else env[b]
        if op=='*':
            cc=[0]*(len(aa)+len(bb)-1)
            for j,x in enumerate(aa):
                if x:
                    for k,y in enumerate(bb): cc[j+k]=(cc[j+k]+x*y)%prime
            while len(cc)>1 and cc[-1]==0: cc.pop()
        else: cc=plus(aa,bb,1 if op=='+' else -1)
        env[n]=cc
    if 'output' in packet:
        actual=[len(env[packet['output']])-1]; expected=[packet['exact_degree']]
    else:
        actual=[len(plus(env[a] if isinstance(a,str) else [a],env[b] if isinstance(b,str) else [b],-1))-1 for a,b in packet['comparisons']]
        expected=packet['residual_exact_degrees']
    require(actual==expected,('degree diagnostic',packet['name'],actual,expected))
    return {'seed':seed,'prime':prime,'degrees':actual,
            'scope':'Supplementary lower-bound diagnostic; PROOF.md gives uniform leading-term proof.'}

def isolated_root_checks():
    total=0
    for rho in (2,3,5):
        Q=rho*rho; d=Q-1; ch,ps=1,0
        for ell in range(1,6):
            ch,ps=rho*ch+(rho*rho-1)*ps,ch+rho*ps
            if ell not in (3,5): continue
            V=-ch//rho
            for f in (-3,2,4):
                D=f*f
                for v in (-2,-1,1,2):
                    z=v*f-V
                    if z<=0: continue
                    M=D+v*v
                    for sy in (-1,1):
                        y=sy*ps; tau=100*(z+abs(y)+1); A=tau*tau
                        t=M*tau+y; e=Q*(D*v*v+z*z)-1; B=2*Q*v*z
                        C=d*(t*t+M*M*A)-e
                        U=C*C+D*B*B-4*d*d*t*t*M*M*A
                        require(U*U-D*(2*C*B)**2==0,'isolated forward identity')
                        fr=Fraction(-U,2*C*B); tr=Fraction(C+B*fr,2*d*t*M)
                        require((fr,tr,t-M*tr)==(f,tau,y),'isolated inverse identity')
                        total+=1
    return {'isolated_components':total,'signed_f_v_y':True,
            'scope':'Algebraic root components, not complete source solutions or K215 runs.'}

def gap_obstruction_checks():
    count=0
    for Q in range(4,120):
        for z in range(2,Q-1):
            require((Q-1)*(2*z+1)>z*z-1,('gap inequality',Q,z))
            count+=1
    return {'exact_small_gap_inequalities':count,'scope':'Supplement only; universal proof is in PROOF.md.'}

def main():
    receipt={'source_pin':PIN,'proof_scope':'Finite algebra/ledger checks, not semantic or proof-assistant verification.',
             'isolated_root_checks':isolated_root_checks(),'gap_checks':gap_obstruction_checks(),'packets':{}}
    for lower in (False,True):
        product,system=build(lower)
        formulas=formula_checks(product,lower)
        for packet in (product,system):
            diagnostics=[polynomial_degree_check(packet,271,1000000007),polynomial_degree_check(packet,272,1000000009)]
            packet['degree_diagnostics']=diagnostics
            (HERE/(packet['name']+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
            receipt['packets'][packet['name']]={'variables':27,'ledger':packet['ledger'],
                'exact_degree':packet.get('exact_degree'),'residual_degrees':packet.get('residual_exact_degrees'),
                'formula_checks':formulas,'degree_diagnostics':diagnostics}
    (HERE/'VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__': main()
