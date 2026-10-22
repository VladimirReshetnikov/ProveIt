#!/usr/bin/env python3
"""Emit and audit 27-integer circuits from pinned, bundled source packets.

Standard-library only. The universal zero-set proof is ODD_SCALE_27_PROOF.md.
These finite computations check arithmetic, not the compiler/Pell theorems.
"""
from __future__ import annotations
from collections import Counter
from pathlib import Path
import copy
import argparse
import hashlib
import json
import random

ROOT=Path(__file__).resolve().parent
INPUT=ROOT/'inputs'
OUTPUT=ROOT.parent/'data/integer27'
POSITIVE=['Jrep','F','alpha','transport_quotient','eta','zeta']
FREE=['f','h','auxiliary_quotient','tau_root','y_aux','gamma']
BASE_NAMES=['Jrep','F','alpha','transport_quotient','f','h','i',
            'auxiliary_quotient','s','w','tau_root','eta','zeta','y_aux','gamma']

def require(ok,message):
    if not ok:
        raise ValueError(message)

def ledger(source):
    cc=Counter(row[1] for row in source)
    return {'operations':len(source),'M':cc['*'],'A':cc['+']+cc['-']}

def prelude():
    source=[]
    names=[]
    for name in POSITIVE:
        u,v,r=(name+'__'+t for t in ('u','v','r'))
        names += [u,v,r]
        source += [
            [name+'__u2','*',u,u], [name+'__v2','*',v,v],
            [name+'__rp1','+',r,1], [name+'__tri','*',r,name+'__rp1'],
            [name+'__two_sq','+',name+'__u2',name+'__v2'],
            [name+'__nonnegative','+',name+'__two_sq',name+'__tri'],
            [name,'+',name+'__nonnegative',1],
        ]
    names += FREE+['i_integer','s_integer','w_integer']
    source += [
        ['i__twice','*',2,'i_integer'], ['i','+','i__twice',1],
        ['s__twice','*',2,'s_integer'], ['s','+','s__twice',1],
        ['w','*','w_integer','w_integer'],
    ]
    require(len(names)==27 and len(source)==47,'substitution count')
    return source,names

def evaluate(packet,inputs):
    env=dict(inputs)
    for name,op,a,b in packet['source']:
        require(name not in env,'reused register')
        x=a if type(a) is int else env[a]
        y=b if type(b) is int else env[b]
        env[name]=x+y if op=='+' else x-y if op=='-' else x*y
    return env

def independent_substitution(env):
    out={n:env[n] for n in FREE}
    for n in POSITIVE:
        u,v,r=(env[n+'__'+suffix] for suffix in ('u','v','r'))
        out[n]=1+u*u+v*v+r*(r+1)
    out['i']=2*env['i_integer']+1
    out['s']=2*env['s_integer']+1
    out['w']=env['w_integer']**2
    return out

def scalar_outputs(packet,env):
    if 'output' in packet:
        return [env[packet['output']]]
    return [(a if type(a) is int else env[a])-(b if type(b) is int else env[b])
            for a,b in packet['comparisons']]

def validate(packet):
    known=set(packet['fixed_numerals']+packet['witnesses'])
    require(len(known)==len(packet['fixed_numerals'])+len(packet['witnesses']),
            'duplicate input port')
    for name,op,a,b in packet['source']:
        require(name not in known and op in ('+','-','*'),'register/operator')
        require(all(type(x) is int or x in known for x in (a,b)),'operand')
        known.add(name)
    outs=([packet['output']] if 'output' in packet else
          [x for pair in packet['comparisons'] for x in pair])
    needed={x for x in outs if isinstance(x,str)}
    for row in reversed(packet['source']):
        require(row[0] in needed,'dead gate '+row[0])
        needed.update(x for x in row[2:] if isinstance(x,str))
    require(set(packet['witnesses']+packet['fixed_numerals'])<=needed,'dead port')

def padd(a,b,sign=1):
    c=[0]*max(len(a),len(b))
    for j,x in enumerate(a): c[j]+=x
    for j,x in enumerate(b): c[j]+=sign*x
    while len(c)>1 and c[-1]==0: c.pop()
    return c

def pmul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        for k,y in enumerate(b): c[j+k]+=x*y
    return c

def specialization(packet):
    # Degree-two positive ports all specialize to t^2+1; odd/square maps
    # remain literal. Only scalar fixed ports are specialized, at beta=15.
    env={name:[0,1] for name in packet['witnesses']}
    for name in POSITIVE:
        env[name+'__v']=[0]
        env[name+'__r']=[0]
    env.update(Bm1=[15],Kconstant=[19],MC=[2],MF=[20])
    for name,op,a,b in packet['source']:
        x=[a] if type(a) is int else env[a]
        y=[b] if type(b) is int else env[b]
        env[name]=pmul(x,y) if op=='*' else padd(x,y,1 if op=='+' else -1)
    return env

def weighted_bounds(base):
    env={n:2 if n in POSITIVE+['w'] else 1 for n in BASE_NAMES}
    env.update({n:0 for n in base['fixed_numerals']})
    for name,op,a,b in base['source']:
        x=0 if type(a) is int else env[a]
        y=0 if type(b) is int else env[b]
        env[name]=x+y if op=='*' else max(x,y)
        if name=='norm_main':
            v=max(env['wn2'],env['gamma']+env['a4m5'])
            env[name]=max(env['R12']+env['R10a']+v,2*v,
                          env['a4m5']+env['c2'])
    return env

def pel(b,n):
    x,y=1,0
    for _ in range(n): x,y=b*x+(b*b-1)*y,x+b*y
    return x,y

def finite_lemma_checks():
    count=0
    for X in range(16,65):
        for Z in range(4,41):
            B=(X+1)*Z-2
            P0=2*X*Z*Z+1
            require(2*B*B-1>P0 and B>Z,'negative-scale parameters')
            require((2*B-1)**2-2*P0*X ==
                4*(2*X+1)*Z*Z-20*(X+1)*Z+25-2*X>0,'ratio identity')
            a=-(X+1)*Z
            A=a+2
            H=4*a+3
            for n in range(1,10):
                chi,psi=pel(A,n)
                require((chi-a*psi-pow(2,n,abs(H)))%H==0,'minus projection')
                require(((chi+a*psi)*pow(2,n,abs(H))-1)%H==0,'plus projection')
            count+=1
    population=0
    for t in range(2,8):
        M=1<<(2*t)
        rng=random.Random(t)
        for _ in range(100):
            S=rng.randrange(1,M)
            T=rng.randrange(M)&(M-1-S)
            R=(M-S)*(M-1)+T
            require(R==(M-1-S)*M+(S+T),'packing identity')
            require(R.bit_count()==2*t+T.bit_count(),'saturation identity')
            population+=1
    # Actual first/main Pell solutions with a negative scale and a strict
    # ratio interval. These need not satisfy the compiler packing constraints;
    # the purpose is to test both forbidden main-root projection signs on
    # exact Pell tuples, not merely on arbitrary parameter identities.
    ratio_cases=0
    root_sign_cases=0
    for X in range(16,41):
        for r in range(2,6):
            center=(X+1)**(2*r)//(2*X**r)
            R=2*r+1
            for Z in range(max(4,center-8),center+9):
                B=(X+1)*Z-2
                P0=2*X*Z*Z+1
                tau,halfb=pel(P0,r+1)
                k=2*halfb
                chi,c0=pel(B,R)
                eta=k*Z-c0
                zeta=k-eta
                if eta<=0 or zeta<=0: continue
                ratio_cases+=1
                a=-(X+1)*Z
                H=4*a+3
                Delta=B*B-1
                c=-c0
                require(tau*tau-X*Z*Z*(X*Z*Z+1)*k*k==1,'first norm')
                require(c==k*(-Z)+eta,'negative strict ratio')
                require(Z>2**R,'large negative scale at exact tuple')
                for D in [chi,-chi]:
                    require(D*D-Delta*c*c==1,'main norm')
                    require((D-X-a*c)%H!=0,'forbidden integral gamma')
                    root_sign_cases+=1
    require(ratio_cases>0,'no exact Pell ratio cases exercised')
    return {'negative_parameter_cases':count,'signed_projection_indices_per_case':9,
            'population_identity_cases':population,'exact_negative_pell_ratio_tuples':ratio_cases,
            'excluded_main_root_sign_cases':root_sign_cases}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, default=OUTPUT)
    args=parser.parse_args()
    output=args.out
    output.mkdir(parents=True,exist_ok=True)
    cases=[
      ('blank_normalized_integer29_poly119.json','normalized27_poly114',114,274,True),
      ('blank_normalized_integer29_poly120.json','normalized27_poly115',115,216,True),
      ('blank_ordinary_integer29_poly121.json','ordinary27_poly116',116,172,True),
      ('ordinary_blank_system60.json','ordinary27_system107',107,46,False),
      ('ordinary_blank_sos77.json','ordinary27_sos124',124,92,False),
    ]
    pre,names=prelude()
    rng=random.Random(202610220327)
    receipts=[]
    for srcname,outname,count,degree,from29 in cases:
        raw=(INPUT/srcname).read_bytes()
        old=json.loads(raw)
        # The source 29-integer packet has 52 substitution gates; removing
        # them restores its literal original 15-port arithmetic circuit.
        base=copy.deepcopy(old)
        if from29:
            require(old['substitution']['added_operations']['operations']==52,
                    'unexpected parent substitution')
            base['source']=old['source'][52:]
            base['witnesses']=BASE_NAMES
        out={key:copy.deepcopy(base[key]) for key in
             ['fixed_numerals','source','output','comparisons'] if key in base}
        out['name']=outname
        out['source']=pre+base['source']
        out['witnesses']=names
        out['witness_domain']='unrestricted integers'
        out['ledger']=ledger(out['source'])
        out['exact_degree' if 'output' in out else 'exact_maximum_degree']=degree
        out['source_parent']={'path':srcname,'sha256':hashlib.sha256(raw).hexdigest(),
          'repository_commit':'f0ae4e0991ca44a7bb4e5671d42e33d775e48035'}
        out['coefficient_interface']='Bind all four ports together using COEFFICIENT_BINDING.json and coefficients/T5263_CONSTANTS.json; the refined compiler proof supplies the required complete blank interface.'
        out['substitution']={'positive_ports':POSITIVE,
          'positive_formula':'1+u^2+v^2+r(r+1)','free_ports':FREE,
          'i':'2*i_integer+1','s':'2*s_integer+1','w':'w_integer^2',
          'added_operations':ledger(pre),'proof':'proofs/ODD_SCALE_27_PROOF.md'}
        validate(out)
        require(out['ledger']['operations']==count,'operation count')
        for _ in range(120):
            vv={n:rng.randrange(-5,6) for n in names}
            fixed={'Bm1':15,'Kconstant':19,'MC':2,'MF':20}
            bb=evaluate(base,{**fixed,**independent_substitution(vv)})
            ee=evaluate(out,{**fixed,**vv})
            require(scalar_outputs(base,bb)==scalar_outputs(out,ee),'substitution')
            a,c,x,g,H=(ee[n] for n in ('R12','R10a','wn2','gamma','a4m5'))
            v=x+g*H
            require(ee['norm_main']==2*a*c*v+v*v-H*c*c,'main cancellation')
        sp=specialization(out)
        upper=weighted_bounds(base)
        if 'output' in out:
            actual=len(sp[out['output']])-1
            require(actual==degree==upper[out['output']],'degree certificate')
            lead=sp[out['output']][-1]
            degs=[actual]
        else:
            degs=[]
            bounds=[]
            for l,r in out['comparisons']:
                ll=[l] if type(l) is int else sp[l]
                rr=[r] if type(r) is int else sp[r]
                degs.append(len(padd(ll,rr,-1))-1)
                bounds.append(max(0 if type(l) is int else upper[l],
                                  0 if type(r) is int else upper[r]))
            require(degs==bounds and max(degs)==degree,'system degree certificate')
            lead=None
            out['residual_exact_degrees']=degs
        (output/(outname+'.json')).write_text(json.dumps(out,indent=2)+'\n')
        receipts.append({'name':outname,'variables':len(names),
          'ledger':out['ledger'],'exact_degree':degree,'specialized_degrees':degs,
          'specialized_leading_coefficient':lead,'random_signed_substitution_cases':120,
          'all_gates_live':True,'all_ports_live':True})
    receipt={'circuits':receipts,'lemmas':finite_lemma_checks(),
      'scope':'Finite polynomial checks only; universal mathematical proof is separate.'}
    (output/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__': main()
