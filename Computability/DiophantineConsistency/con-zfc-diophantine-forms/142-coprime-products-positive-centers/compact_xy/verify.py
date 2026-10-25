#!/usr/bin/env python3
"""Independent exact checks for the complete XY-carrier equations.

No builder or upstream executable is imported. Finite checks do not prove
the unbounded Pell/native calibration theorem; see PROOF.md.
"""
from __future__ import annotations
import argparse
from collections import Counter
from copy import deepcopy
import gzip
import hashlib
import json
from pathlib import Path
import random

ROOT=Path(__file__).resolve().parent
INPUTS=['J','F','alpha','i','T','w','s','n','eta','zeta']
PORTS=['beta','K0','MC','MF']
SYMBOLS=INPUTS+PORTS
ZERO=(0,)*len(SYMBOLS)

def require(p,msg):
    if not p: raise ValueError(msg)

def const(n): return {ZERO:n} if n else {}
def variable(name):
    e=list(ZERO);e[SYMBOLS.index(name)]=1;return {tuple(e):1}
def plus(a,b,sign=1):
    r=dict(a)
    for m,c in b.items():
        r[m]=r.get(m,0)+sign*c
        if not r[m]: del r[m]
    return r
def times(a,b):
    r={}
    for x,c in a.items():
        for y,d in b.items():
            m=tuple(u+v for u,v in zip(x,y));r[m]=r.get(m,0)+c*d
    return {m:c for m,c in r.items() if c}
def power(a,n):
    r=const(1)
    while n:
        if n&1:r=times(r,a)
        n//=2
        if n:a=times(a,a)
    return r

def leading_graph(d):
    env={s:(1 if s in INPUTS else 0,variable(s)) for s in SYMBOLS}
    def get(x):return (0,const(x)) if isinstance(x,int) else env[x]
    for name,op,a,b in d['source']:
        da,pa=get(a);db,pb=get(b)
        if op=='*': degree=da+db;p=times(pa,pb)
        else:
            degree=max(da,db)
            p=plus(pa if da==degree else {},pb if db==degree else {},1 if op=='+' else -1)
        require(bool(p),'Highest terms cancel at '+name+'; complete next-degree analysis required')
        require(all(sum(m[:10])==degree for m in p),'Wrong grading at '+name)
        env[name]=(degree,p)
    return env

def expected_leading(d):
    q0=times(variable('beta'),variable('J'))
    k0=plus(variable('eta'),variable('zeta'))
    t0=plus(variable('T'),variable('alpha')) if d['auxiliary_T_shift'] else variable('T')
    partial=d['retain_fraction_s_over_q']
    if d['transport_weight']=='V^2':
        factors=[(q0,272 if partial else 378),(variable('w'),46 if partial else 48),(variable('s'),108 if partial else 110),
                 (variable('i'),20),(k0,64),(t0,4),
                 (plus(plus(q0,variable('F'),-1),variable('alpha'),-1),2)]
        p=const(2**14)
    else:
        factors=[(q0,206 if partial else 284),(variable('w'),34 if partial else 36),(variable('s'),80 if partial else 82),
                 (variable('i'),14),(k0,46),(t0,2)]
        p=const(-2**10)
    for a,n in factors:p=times(p,power(a,n))
    return p

def graph_values(d,inputs,ports,modulus=None):
    env={**inputs,**ports}
    def get(x):return x if isinstance(x,int) else env[x]
    for name,op,a,b in d['source']:
        u,v=get(a),get(b)
        x=u+v if op=='+' else u-v if op=='-' else u*v
        env[name]=x if modulus is None else x%modulus
    return env

def formula(inputs,ports,weight,shift,partial=False,modulus=None):
    J,F,alpha,i,T,w,s,n,eta,zeta=(inputs[x] for x in INPUTS)
    beta,K0,MC,MF=(ports[x] for x in PORTS)
    q=beta*J+1;h=q-1;C=q-F-alpha;X=w*q;Y=q**(2 if partial else 3)*s
    D=X*Y;k=eta+zeta;c=k*Y+eta;A=Y*(X+1)+1
    Delta=A*A-1;H=4*A-5;V0=X*Y*Y;E=1+V0*(V0+1)*k*k
    R=(h*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    e=k-R-1;B=(K0+w)*C-F;U=i*c*c;a=Delta*U*U*E
    F0=1+a;G=E*F0;Fsq=(1+2*a)**2;Q=4*Delta*Delta*U*U*G
    b=c*(T+alpha if shift else T)-R;V=Fsq*b-c
    L=V*V if weight=='V^2' else b*V
    Dc=q**5 if partial else D
    ec=e-s*q**4 if partial else e
    Kpos=X*(3*c-2*X)+2;M=h*Dc*H
    Z=h*Dc*(H*(n-L*B)+Kpos)-H*(Dc*B+h*ec)
    N=(Q-1)*Z*Z-M*M*G*(Q*V*V-1)
    vals={'q':q,'Y':Y,'D':D,'Am1':A-1,'Delta':Delta,'Hp':H,'V0':V0,
          'Dtau':E,'R':R,'e':e,'Bt':B,'U':U,'DpI2':a,'Df':F0,
          'Dg':G,'Fsqr':Fsq,'Q':Q,'cTR':b,'V':V,'Mtot':M,'Znum':Z,'N':N}
    return {k:(v if modulus is None else v%modulus) for k,v in vals.items()}

def topology(d):
    require(d['witnesses']==INPUTS,'Witness signature')
    require(d['fixed_numerals']==PORTS,'Port signature')
    require(d['domain']=='strictly positive integers','Domain')
    known=set(INPUTS+PORTS);parents={};count=Counter()
    for row in d['source']:
        require(isinstance(row,list) and len(row)==4,'Row schema')
        name,op,a,b=row
        require(isinstance(name,str) and name not in known,'Definition uniqueness')
        require(op in ['+','-','*'],'Binary primitive')
        require(all(isinstance(x,int) or x in known for x in [a,b]),'Topology')
        known.add(name);parents[name]=[x for x in [a,b] if isinstance(x,str)];count[op]+=1
    require(d['output']=='N' and 'N' in parents,'Output')
    used=set();stack=['N']
    while stack:
        x=stack.pop()
        if x in used:continue
        used.add(x);stack+=parents.get(x,[])
    require(used==known,'Dead rows/inputs/ports: '+str(known-used))
    require(d['operations']==len(parents),'Operation count')
    require(d['operation_breakdown']==dict(count),'Operation breakdown')
    return count

def literal_transfer(d):
    path=ROOT/d['parent'];raw=path.read_bytes()
    require(hashlib.sha256(raw).hexdigest()==d['parent_sha256'],'Parent hash')
    p=json.loads(raw);old=p['source'];new=d['source'];wanted=[]
    shift=d['auxiliary_T_shift']
    for row in old:
        name,op,a,b=row
        if name=='Xp1':wanted.append(['D','*','X','Y'])
        elif name=='Y2' or name=='Tp' and not shift:pass
        elif name=='Am1':wanted.append(['Am1','+','D','Y'])
        elif name=='V0':wanted.append(['V0','*','D','Y'])
        else:
            mapping={'Y2':'D'}
            if not shift:mapping['Tp']='T'
            wanted.append([name,op,mapping.get(a,a),mapping.get(b,b)])
    if d['retain_fraction_s_over_q']:
        partial=[]
        for name,op,a,b in wanted:
            if name=='q3':continue
            if name=='Y':a='q2'
            elif name=='P1mu2':b='D1'
            elif name=='mu2inner':a='D1'
            elif name=='P1e':
                partial += [['sE0','*','s','E0'],['eclear','-','e','sE0']]
                b='eclear'
            partial.append([name,op,a,b])
            if name=='Y':partial += [['E0','*','q2','q2'],['D1','*','q','E0']]
        wanted=partial
    require(wanted==new,'Literal full row transformation')
    require(d['coefficient_binding']==p['coefficient_binding'],'Whole coefficient binding')

def coefficients(d):
    vals={}
    for port in PORTS:
        meta=d['coefficient_binding']['ports'][port]
        raw_gz=(ROOT/'coefficients'/meta['file']).read_bytes()
        require(hashlib.sha256(raw_gz).hexdigest()==meta['gzip_sha256'],'Gzip hash '+port)
        raw=gzip.decompress(raw_gz)
        require(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'],'Raw hash '+port)
        n=int.from_bytes(raw,'little')
        require(n.bit_length()==meta['bits'],'Bit length '+port)
        require(raw==n.to_bytes((n.bit_length()+7)//8,'little'),'Canonical bytes '+port)
        vals[port]=n
    require(vals['beta']>=31 and vals['beta']%2==1 and vals['K0']>0
            and 0<vals['MC']<vals['beta']<vals['MF']<2*vals['beta'],'Port box')
    return vals

def check(d):
    counts=topology(d);literal_transfer(d);ports=coefficients(d)
    leads=leading_graph(d)
    require(leads['N'][0]==d['exact_degree'],'Exact degree')
    require(leads['N'][1]==expected_leading(d),'Complete leading polynomial')
    rng=random.Random(20261025)
    # Signed sample points check polynomial formulas even outside the positive
    # solution domain; they do not claim to prove mathematical soundness.
    points=[dict(zip(INPUTS,[rng.randrange(-2,5) for _ in INPUTS])) for _ in range(20)]
    small={'beta':31,'K0':11,'MC':7,'MF':47}
    for inp in points:
        got=graph_values(d,inp,small);wanted=formula(inp,small,d['transport_weight'],d['auxiliary_T_shift'],d['retain_fraction_s_over_q'])
        require(all(got[k]==v for k,v in wanted.items()),'Independent exact formula')
    for prime in [2**61-1,2**89-1]:
        ps={k:v%prime for k,v in ports.items()}
        for _ in range(10):
            inp={x:rng.randrange(1,17) for x in INPUTS}
            got=graph_values(d,inp,ps,prime)
            wanted=formula(inp,ps,d['transport_weight'],d['auxiliary_T_shift'],d['retain_fraction_s_over_q'],prime)
            require(all(got[k]==v for k,v in wanted.items()),'Actual tuple modular formula')
    return {'operations':len(d['source']),'operation_breakdown':dict(counts),
            'exact_degree':leads['N'][0],'complete_leading_monomials':len(leads['N'][1]),
            'register_degrees':{x:leads[x][0] for x in ['D','Am1','Q','V','Dg','Mtot','Znum','N']},
            'exact_integer_formula_points':len(points),'actual_tuple_modular_points':20}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',default=None);args=ap.parse_args()
    results={}
    for p in sorted(ROOT.glob('equation_*.json')):
        d=json.loads(p.read_text());results[p.name]=check(d)
    require(len(results)==6,'Expected six complete equations')
    d=json.loads((ROOT/'equation_76_626.json').read_text())
    corrupt=[]
    m=deepcopy(d);m['domain']='integers';corrupt.append(m)
    m=deepcopy(d);m['source'][next(i for i,r in enumerate(m['source']) if r[0]=='D')][2]='q';corrupt.append(m)
    m=deepcopy(d);m['exact_degree']-=1;corrupt.append(m)
    m=deepcopy(d);m['source'][-1][1]='-';corrupt.append(m)
    m=deepcopy(d);m['coefficient_binding']['ports']['beta']['raw_sha256']='0'*64;corrupt.append(m)
    for m in corrupt:
        rejected=False
        try:check(m)
        except ValueError:rejected=True
        require(rejected,'Accepted mutated artifact')
    result={'status':'pass','circuits':results,'actual_artifact_mutations_rejected':len(corrupt),
            'proof_boundary':'Exact finite artifact/algebra checks; unbounded theorem is PROOF.md plus named inherited calibration.'}
    text=json.dumps(result,indent=2)+'\n'
    if args.output:Path(args.output).write_text(text)
    print(text,end='')

if __name__=='__main__':main()
