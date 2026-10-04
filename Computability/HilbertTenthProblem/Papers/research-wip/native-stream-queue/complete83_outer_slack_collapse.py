#!/usr/bin/env python3
"""Data-only full83 outer-slack collapse audit; no predecessor code executes."""
import argparse
import copy
from collections import Counter
from fractions import Fraction
import hashlib
import json
from math import gcd,lcm
from pathlib import Path

PINS={
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete75_weakened86_all_input_collapse.py':'ab7a3280915a569a6fb18adc3ab5acb0a917748664d146a6a655eb3c5ac16685',
 'complete75_weakened86_all_input_collapse.json':'5a77d0d95ad4ea3c61c3d5c82c9c159c7348a1ad3be2b1057a51e05b1c212736',
 'complete75_weakened86_all_input_collapse.md':'46f3e0f25fc4efeb3f8129b77c3df988283c7a818ee2af330e8e8f460dc8d017',
 'complete75_weakened86_auxiliary_sign_lift.md':'491ac3c3755efed1c6c89f7e07a752c25fb040859cac8c07d7db25e803c62c53',
 'complete75_weakened86_infinite_outer_family.md':'74b6c968500c5177440096bd3da3c9c07f9208f10aea79cad73554e9814bf1a2',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'complete75_weakened86_rejecting_compiler.md':'186fc8a89c99455361fd0eb0b90d53c1fa90af32191a741c02e950d3bb0d8e78'}

def need(test,msg):
    if not test:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
    if type(a) is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b
def pairs(items):
    d={}
    for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
    return d
def read(path):return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=lambda s:(_ for _ in ()).throw(ValueError(s)))

class Poly:
    def __init__(self,v=0):
        if isinstance(v,Poly):self.c=dict(v.c)
        elif isinstance(v,dict):self.c={m:z for m,z in v.items() if z}
        else:self.c={():Fraction(v)} if v else {}
    def __add__(self,b):
        out=dict(self.c)
        for m,z in Poly(b).c.items():out[m]=out.get(m,0)+z
        return Poly(out)
    __radd__=__add__
    def __neg__(self):return Poly({m:-z for m,z in self.c.items()})
    def __sub__(self,b):return self+-Poly(b)
    def __rsub__(self,b):return Poly(b)+-self
    def __mul__(self,b):
        out={}
        for m,z in self.c.items():
            for n,w in Poly(b).c.items():
                key=tuple(sorted(m+n));out[key]=out.get(key,0)+z*w
        return Poly(out)
    __rmul__=__mul__
    def __eq__(self,b):return self.c==Poly(b).c

def atom(s):return Poly({(s,):1})
def operation(op,a,b):return a+b if op=='+' else a-b if op=='-' else a*b

def build(parent):
    source=[]
    for row in parent['source']:
        name,op,a,b=row
        if name=='q_minus_FZ':continue
        if name=='C_after_alpha':row=[name,'-','q_minus_F','alpha_sum']
        elif name=='gap_product':row=[name,'*','q','q_minus_F']
        elif name=='gap':row=[name,'-','gap_product','Z']
        source.append(list(row))
    return dict(source=source,free=['alpha_sum' if x=='alpha' else x for x in parent['free']],
      witnesses=['alpha_sum' if x=='alpha' else x for x in parent['witnesses']],
      factors=list(parent['factors']),fixed_numerals=copy.deepcopy(parent['fixed_numerals']),
      ordinary_input=copy.deepcopy(parent['ordinary_input']),output=parent['output'],
      ledger=dict(M=47,A=36,total=83),exact_degree=187,syntactic_degree_upper=197,
      status='REFUTED_ALL_POSITIVE_INPUTS_ON_VALID_COMPILER_SLICES',
      all_ring_relation='P83(alpha_sum)=P84(alpha=alpha_sum-Z)',
      positive_forward_map='alpha_sum=alpha+Z; all other supplied coordinates unchanged',
      positive_inverse='Only when alpha_sum>Z; false-input zeros have alpha_sum<Z',
      scope='Full18-positive-witness83 polynomial refuted on inherited valid fixed-program slices; other coefficient recipes are not assessed.')

def evaluate(packet,values):
    need(set(values)==set(packet['free']),'exact source interface');env=dict(values);parents={};ops=Counter()
    for name,op,a,b in packet['source']:
        need(name not in env and op in ('+','-','*'),'SSA row')
        for z in (a,b):need(type(z) is int or (type(z) is str and z in env),'closed row')
        av=env[a] if type(a) is str else a;bv=env[b] if type(b) is str else b
        env[name]=operation(op,av,bv);parents[name]=[z for z in (a,b) if type(z) is str];ops[op]+=1
    need(packet['output']==packet['source'][-1][0],'last paid output')
    live=set();pending=[packet['output']]
    while pending:
        x=pending.pop()
        if x not in live:live.add(x);pending.extend(parents.get(x,[]))
    need(live==set(env),'every paid row and supplied port live')
    return env,dict(M=ops['*'],A=ops['+']+ops['-'],total=sum(ops.values()))

def graph_proof(parent,child):
    old={v:atom(v) for v in parent['free']};new={v:atom(v) for v in child['free']}
    old['alpha']=atom('alpha_sum')-atom('Z')
    child_rows={r[0]:r for r in child['source']};proved=[]
    for name,op,a,b in parent['source']:
        old[name]=operation(op,old[a] if type(a) is str else a,old[b] if type(b) is str else b)
        if name not in child_rows:
            need(name=='q_minus_FZ','only deleted register');continue
        _,cop,ca,cb=child_rows[name]
        new[name]=operation(cop,new[ca] if type(ca) is str else ca,new[cb] if type(cb) is str else cb)
        if name=='gap_product':continue
        need(old[name]==new[name],'all-value register identity '+name);proved.append(name)
        if name!='q':old[name]=new[name]=atom(name)
    need(len(proved)==82 and child['output'] in proved,'complete inductive graph proof')
    counts=Counter(arg for row in parent['source'] for arg in row[2:] if type(arg) is str)
    need(counts['q_minus_FZ']==2 and counts['alpha']==1,'private producer closure')
    return dict(equal_registers=proved,private_changed_product='gap_product',
      deleted_register='q_minus_FZ',full_output=True,all_ring=True,
      exact_degree_reason='Invertible linear substitution alpha=alpha_sum-Z preserves inherited uniform exact187.')

def pell(A,n,mod=None):
    D=A*A-1;out=(1,0);base=(A,1)
    def mul(x,y):
        r=(x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
        return tuple(z%mod for z in r) if mod else r
    while n:
        if n&1:out=mul(out,base)
        base=mul(base,base);n//=2
    return out

def wrap(M,K):
    for omega in (-1,1):
      for sign_t in (-1,1):
       for sigma in (-1,1):
        r=(omega+sign_t*(M*sigma-K))%(6*M)
        for j in (r,(r+3*M)%(6*M)):
            if j%2==0 and 0<j<2*M:return dict(omega=omega,t=sign_t,sigma=sigma,j=j)
    raise ValueError('missing even wrap')

def wrap_checks():
    cases=0;exceptional=0
    for M in list(range(3,80,2))+[255,1023]:
        for K in range(0,6*M,2):
            d=wrap(M,K);j=d['j']
            need((j-d['omega']-d['t']*(M*d['sigma']-K))%(3*M)==0,'wrap congruence')
            need(j%2==0 and 0<j<2*M,'strict even wrap range');cases+=1
            exceptional+=int((M-K+1)%(2*M)==0)
    return dict(cases=cases,old_four_sign_exceptional_cases=exceptional,
                lemma='All odd M>=3 and even K; eight independent omega,t,sigma signs suffice.')

def prime_certificate(c):
    n=c['n']
    if n==2:need(c=={'n':2},'prime base');return 1
    factors=c['factors'];children=c['children'];need([z['n'] for z in children]==[p for p,e in factors],'prime child list')
    product=1;count=1
    for (p,e),z in zip(factors,children):
        need(type(e) is int and e>0,'prime exponent');product*=p**e;count+=prime_certificate(z)
    need(product==n-1 and pow(c['base'],n-1,n)==1,'Lucas product/power')
    for p,e in factors:need(gcd(pow(c['base'],(n-1)//p,n)-1,n)==1,'Lucas prime factor test')
    return count

def host_checks(host):
    A,H,E,P,M,e,L,ell,X=(host[k] for k in ('A','H','E','P','M','e','L','ell','X'))
    a=A-2;D=A*A-1;MH=M*H
    need(H==4*A-5==3*ell and gcd(L,MH)==3*M,'host period gcd')
    need(pell(A,L,MH)==(1,0) and pow(2,L,H)==1,'Pell and exponential return')
    TE=host['Pell_return_E'];need(pell(A,TE,E)==(1,0),'E return')
    need(e%4==3 and pell(A,e,3*M)[1]==1,'host sign t=1')
    records=[]
    for K in range(0,6*M,2):
      for omega in (-1,1):
       for sigma in (-1,1):
        j=(omega+M*sigma-K)%(3*M)
        if j%2: j+=3*M
        if not 0<j<2*M:continue
        for u in (3,5,11):
            v=u if sigma==-1 else A*u
            ch,ps=pell(A,v,MH);Fv=(ch+a*ps)%MH
            need(Fv%3==sigma%3 and pell(A,v,D)[1]==u,'input congruences')
            ce=pell(A,e,MH)[1];N0=(K-omega*e+j*ce-M*Fv)%MH
            need(N0%(3*M)==0,'new fixed-minus rho congruence')
            z=(N0//(3*M))*pow(omega*(L//(3*M)),-1,ell)%ell
            pb=e+L*z;cp=pell(A,pb,MH)[1]
            need((K-omega*pb+j*cp-M*Fv)%MH==0,'rho progression solution')
            S=lcm(L*ell,E,TE);cE=pell(A,pb,E)[1]
            target=(omega*pb-j*cE-1)%E
            need(target%2==0,'new first index parity');n0=target//2
            for k in (0,1,2,7):
                p=pb+S*k;cmod=pell(A,p,MH)[1]
                need((K-omega*p+j*cmod-M*Fv)%MH==0,'rho progression remains integral')
                need(p%4==3 and pell(A,p,E)[1]==cE and p%E==pb%E,'preserved target residues')
                chp,cph=pell(A,p,H);need((chp-a*cph-X)%H==0,'main gamma integrality')
                need((2*n0-omega*p+j*cE+1)%E==0,'fixed epsilon minus-one index')
            records.append(dict(K=K,omega=omega,sigma=sigma,j=j,u=u,p_base=str(pb),first_n0=str(n0)))
    need(records,'nonempty new CRT hosts')
    return dict(scope='Modular diagnostic q=2 host, not a valid full compiler zero.',
      prime_certificate_nodes=prime_certificate(host['prime_certificate']),records=records)

def aux_checks():
    records=[]
    for A in (2,3,4):
      p=3;c=pell(A,p)[1];D=A*A-1;m=p*c;f,psi=pell(A,m);need(psi%(c*c)==0,'normalized coefficient integral')
      i=psi//(c*c);S=D*psi
      for omega in (-1,1):
        R=omega*p-10000*c;ell=p if omega==1 else p+2*m
        extensions=0
        while True:
            numerator,y=pell(S,ell);need(numerator%S==0,'odd auxiliary quotient');V=numerator//S
            if V>abs(R)*f*f+c:break
            ell+=4*m;extensions+=1;need(extensions<3,'bounded host only')
        need((V+c)%f==0 and (V+R)%c==0,'auxiliary target congruences')
        N=V+c+R*f*f;need(N%(c*f)==0 and N>0,'positive Bezout quotient')
        T=N//(c*f);need(c*(T*f-1)-R*f*f==V,'actual new V')
        need(f*f-D*i*i*c**4==1,'strong norm')
        need(S*S*(V*V-y*y)+y*y==1,'actual auxiliary norm')
        need(D*f*f-S*S==D,'scaled strong factor')
        records.append(dict(A=A,p=p,c=c,R=R,omega=omega,ell=ell,extensions=extensions,
         f_bits=f.bit_length(),V_bits=V.bit_length(),T_bits=T.bit_length(),
         V_sha256=sha(hex(V).encode()),T_sha256=sha(hex(T).encode())))
    return dict(scope='Six fully materialized auxiliary blocks only; no full83 compiler tuple.',records=records)

def numeric(parent,child):
    cases=0;rational=0
    for k in range(48):
        v={name:((k+3)*(j+5)%17+1) for j,name in enumerate(child['free'])}
        if k%2:
            v={name:Fraction(z,j%3+1) for j,(name,z) in enumerate(v.items())};rational+=1
        old=dict(v);old['alpha']=old.pop('alpha_sum')-old['Z']
        a,ca=evaluate(parent,old);b,cb=evaluate(child,v)
        need(cb==child['ledger'] and ca==dict(M=47,A=37,total=84),'full paid graph ledgers')
        for name in child['factors']+[child['output']]:need(a[name]==b[name],'full factor/output identity')
        cases+=1
    # Actual complete multiplication/subtraction finalizer at formal factor cuts.
    formal={name:atom(name) for name in child['factors']};formal['A']=atom('Delta')
    for name,op,a,b in child['source']:
        if name in ('norm_pair','norm_triple','norm_four','norm_product','all_units','seven_units','polynomial'):
            formal[name]=operation(op,formal[a],formal[b])
    product=Poly(1)
    for name in child['factors']:product=product*atom(name)
    need(formal[child['output']]==product-atom('Delta'),'entire formal seven-factor finalizer')
    values=dict(zip(child['factors'],[1,1,1,1,-1,-1,7]));values['A']=7
    for row in child['source']:
        name,op,a,b=row
        if name in ('norm_pair','norm_triple','norm_four','norm_product','all_units','seven_units','polynomial'):
            values[name]=operation(op,values[a],values[b])
    need(values[child['output']]==0,'actual complete target-Delta finalizer')
    return dict(full_identities=cases,rational_cases=rational,
       formal_factorization=True,intended_factors=['1','1','1','1','-1','-1','Delta'],complete_output='0')

def verify(root):
    for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'pin '+name)
    parent=read(root/'complete84_scaled_strong_output.json')['packet'];child=build(parent)
    need(len(child['witnesses'])==18 and len(child['source'])==83,'complete count/interface')
    proof=graph_proof(parent,child);num=numeric(parent,child)
    degrees={v:0 if v in child['fixed_numerals'] else 1 for v in child['free']}
    for name,op,a,b in child['source']:
        da=degrees[a] if type(a) is str else 0;db=degrees[b] if type(b) is str else 0
        degrees[name]=da+db if op=='*' else max(da,db)
    need(degrees[child['output']]==197,'separate syntactic upper')
    host=read(root/'complete75_weakened86_all_input_collapse.json')['modular_host']
    return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=copy.deepcopy(PINS),
      packet=child,graph_proof=proof,numeric=num,wrap=wrap_checks(),modular_host=host_checks(host),auxiliary=aux_checks(),
      theorem='Every positive ordinary input has infinitely many full positive83 zeros on every valid inherited fixed compiler slice.',
      existence_dependencies=['Dirichlet theorem on coprime prime progressions','irrational rotation with inherited exact conjugate-error estimate','normalized positive auxiliary Pell lift with arbitrarily large index'],
      full_compiler_zero_materialized=False,established_universal_bound=84)

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',required=True,type=Path)
    q=p.add_mutually_exclusive_group(required=True);q.add_argument('--output',type=Path);q.add_argument('--expect',type=Path)
    a=p.parse_args();out=verify(a.root)
    if a.expect:need(exact(out,read(a.expect)),'type-exact receipt')
    else:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',ledger=out['packet']['ledger'],degree=187,wrap=out['wrap'],
      modular_host_cases=len(out['modular_host']['records']),auxiliary_blocks=len(out['auxiliary']['records']))))
if __name__=='__main__':main()
