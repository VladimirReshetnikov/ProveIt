#!/usr/bin/env python3
"""Independent literal-source, uniform-degree and conditional-sector review."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import random

STEM='complete82_auxiliary_square_product_chart'
AUTHOR={'.py':'5ff4a91d10551eafedd1d44673f64f10aa2ed283ab071d2c969d38410999f6dc',
 '.json':'7c029ad047c9db4652621334cb4c57d1781b5833dfac19de734ef0cb4c05fc7a',
 '.md':'10b83a1800550674298c797e97f4e3ccadb45e7f4c532045e869e03b55caf1c9'}
PINS={
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'review_complete84_scaled_strong_output.md':'6379d0ea3e7befded4be709c1f785a0e81dd915e813608db9b0a32ffbaf9b330',
 '../../1980/HALF_PARAMETER_PELL_92_PROOF.md':'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
 'first_index_scaled_obstruction.md':'b67d208d4c18e45145cf91f272d72e2852c09d79be631da8f0a0ce5f377ba1fd',
 'first_index_scaled_obstruction.json':'52b04d7d47065b822d174f6d480fc31d40d908cc014d4fe517600f2b14ac1cea',
 'free_coefficient83_native_alias.md':'542775d7ff0ccd84f5fe94c32d6c396ad45a8cc033dd1cbd37ed72dedd40f96f',
 'free_coefficient83_native_alias.json':'9bf5e1c6452c5c5700821adaf63d59df1c61d2968704a23e63aae3cac067e846'}
FIXED=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']

def need(ok,msg):
    if not ok:raise ValueError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def exact(a,b):
    if type(a) is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def P(x):return {(x,):1} if type(x) is str else {():x} if x else {}
def add(a,b):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,0)+c
    return {m:c for m,c in out.items() if c}
def scale(a,n):return {m:c*n for m,c in a.items() if c*n}
def sub(a,b):return add(a,scale(b,-1))
def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(sorted(m+n));out[key]=out.get(key,0)+c*d
    return {m:c for m,c in out.items() if c}
def power(a,n):
    out=P(1)
    while n:
        if n&1:out=mul(out,a)
        n//=2
        if n:a=mul(a,a)
    return out
OPS={'+':add,'-':sub,'*':mul}

def source_graph(parent,child):
    removed=[['L16','*','f','f'],['auxiliary_Tf','*','auxiliary_quotient','f']]
    expected=[r for r in parent['source'] if r not in removed]
    need(all(parent['source'].count(r)==1 for r in removed),'two actual deleted producers')
    need(child['source']==expected,'all 82 rows exactly retained in order')
    rename={'f':'L16','auxiliary_quotient':'auxiliary_Tf'}
    for field in ('free','witnesses'):
        need(child[field]==[rename.get(x,x) for x in parent[field]],'exact '+field+' projection')
    for field in ('fixed_numerals','ordinary_input','output','factors'):
        need(child[field]==parent[field],'unchanged '+field)
    need(child['fixed_numerals']==FIXED and child['factors']==FACTORS,'fixed interface')
    need(len(child['witnesses'])==18 and len(child['free'])==25,'coordinate counts')
    uses={x:[r[0] for r in parent['source'] if x in r[2:]] for x in ('f','auxiliary_quotient','i','y_aux')}
    need(uses=={'f':['L16','auxiliary_Tf'],'auxiliary_quotient':['auxiliary_Tf'],'i':['aux_coefficient_root'],'y_aux':['aux_y2']},'all old private consumers')
    known=set(child['free']);table={}
    for name,op,a,b in child['source']:
        need(name not in known and op in OPS,'SSA')
        need(all(type(v) is int or type(v) is str and v in known for v in (a,b)),'closed source')
        known.add(name);table[name]=(op,a,b)
    live=set();stack=[child['output']]
    while stack:
        v=stack.pop()
        if type(v) is int or v in live:continue
        live.add(v)
        if v in table:stack.extend(table[v][1:])
    need(live==known,'all rows and coordinates live')
    counts=Counter(row[1] for row in child['source'])
    need((counts['*'],counts['+']+counts['-'],len(table))==(45,37,82),'fully paid 82')
    need(child['ledger']==dict(M=45,A=37,total=82,core_M=39,core_A=36,core_total=75,finalizer_M=6,finalizer_A=1,finalizer_total=7),'all ledger fields')
    # Exact expression interning compares all retained registers after f^2,T*f.
    intern={}
    def node(key):
        if key not in intern:intern[key]=len(intern)
        return intern[key]
    def run(p,env):
        for n,o,a,b in p['source']:
            env[n]=node((o,env[a] if type(a) is str else node(('integer',a)),env[b] if type(b) is str else node(('integer',b))))
        return env
    pe=run(parent,{v:node(('variable',v)) for v in parent['free']})
    ce=run(child,{v:pe[v] if v in ('L16','auxiliary_Tf') else node(('variable',v)) for v in child['free']})
    need(all(pe[n]==ce[n] for n in table),'full 82-register polynomial pullback')
    return table,uses

def expand_at(table,root,cuts):
    memo={x:P(x) for x in cuts}
    def rec(x):
        if type(x) is int:return P(x)
        if x not in memo:
            o,a,b=table[x];memo[x]=OPS[o](rec(a),rec(b))
        return memo[x]
    return rec(root)

def full_relation(table):
    outer=['norm_first','norm_main','norm_input','norm_index','norm_transport']
    cuts=outer+['A','R10a','r_lhs','i','L16','auxiliary_Tf','y_aux']
    actual=expand_at(table,'polynomial',cuts)
    D,c,R,i,F,U,y=map(P,['A','R10a','r_lhs','i','L16','auxiliary_Tf','y_aux'])
    K=mul(power(i,2),mul(power(D,2),power(c,4)))
    V=sub(mul(c,sub(U,P(1))),mul(R,F))
    Na=add(mul(K,sub(power(V,2),power(y,2))),power(y,2))
    Qs=sub(F,mul(D,mul(power(i,2),power(c,4))))
    five=P(1)
    for n in outer:five=mul(five,P(n))
    wanted=mul(D,sub(mul(five,mul(Na,Qs)),P(1)))
    need(actual==wanted,'entire literal finalizer/cofactor identity')
    return {'terms':len(actual),'coefficient_sha256':digest(stable([[list(m),v] for m,v in sorted(actual.items())]))}

def uniform_degree(child,table):
    # Authenticate the source cones before the only two cancellation rewrites.
    guarded={
      'R12':('+','UM','sn2'),'cam2':('*','R10a','R12'),'D1':('+','wn2','cam2'),
      'gamma_sum':('+','rho','sigma'),'a4':('*',4,'R12'),'a4m5':('+','a4',3),
      'gam':('*','gamma_sum','a4m5'),'R14':('+','D1','gam'),'L15':('*','R14','R14'),
      'a_square':('*','R12','R12'),'A':('+','a_square','a4m5'),'c2':('*','R10a','R10a'),
      'Ac2':('*','A','c2'),'norm_main':('-','L15','Ac2'),
      'difference_multiple':('*','index_rhs','R12'),'exponent_partial':('+','W','difference_multiple'),
      'modulus_multiple':('*','rho','a4m5'),'exponent_rhs':('+','exponent_partial','modulus_multiple'),
      'mu2':('*','exponent_rhs','exponent_rhs'),'kappa2':('*','index_rhs','index_rhs'),
      'scaled_kappa2':('*','A','kappa2'),'norm_input':('-','mu2','scaled_kappa2')}
    need(all(table[k]==v for k,v in guarded.items()),'actual main/input cancellation producers')
    a,c,H,z=map(P,['a','c','H','z'])
    original=sub(power(add(mul(a,c),z),2),mul(add(power(a,2),H),power(c,2)))
    lowered=sub(add(power(z,2),scale(mul(a,mul(c,z)),2)),mul(H,power(c,2)))
    need(original==lowered,'general exact norm cancellation')
    # Degree/leading homogeneous polynomial pairs over Z[all six fixed numerals].
    env={v:(0 if v in FIXED else 1,P(v)) for v in child['free']}
    def plus(u,v,sign=1):
        d=max(u[0],v[0]);p={}
        if u[0]==d:p=add(p,u[1])
        if v[0]==d:p=add(p,scale(v[1],sign))
        need(bool(p),'unexpected unproved highest-degree cancellation')
        return d,p
    def times(u,v):return u[0]+v[0],mul(u[1],v[1])
    def get(v):return env[v] if type(v) is str else (0,P(v))
    def norm(a,c,H,z):
        return plus(plus(times(z,z),times((0,P(2)),times(a,times(c,z)))),times(H,times(c,c)),-1)
    for n,o,a,b in child['source']:
        if n=='norm_main':
            z=plus(get('wn2'),times(get('gamma_sum'),get('a4m5')))
            env[n]=norm(get('R12'),get('R10a'),get('a4m5'),z)
        elif n=='norm_input':
            z=plus(get('W'),times(get('rho'),get('a4m5')))
            env[n]=norm(get('R12'),get('index_rhs'),get('a4m5'),z)
        else:env[n]=times(get(a),get(b)) if o=='*' else plus(get(a),get(b),1 if o=='+' else -1)
    degrees=[env[n][0] for n in FACTORS]
    need(degrees==[22,18,32,58,7,2,46] and env['polynomial'][0]==185,'all exact source degrees')
    Q=mul(P('Bm1'),P('Jrep'));k=add(P('eta'),P('zeta'));gamma=add(P('rho'),P('sigma'))
    C1=sub(sub(sub(sub(Q,P('F')),P('Z')),P('alpha')),mul(P('twice_cell_bits'),P('x')))
    Nt=sub(mul(P('w'),C1),mul(P('transport_quotient'),Q))
    expected=P(32)
    for pol,e in ((Q,111),(P('h'),1),(gamma,1),(P('delta'),2),(P('i'),4),(k,13),(P('w'),18),(P('s'),31),(Nt,1),(P('auxiliary_Tf'),2)):
        expected=mul(expected,power(pol,e))
    need(env['polynomial'][1]==expected,'full uniform leading polynomial')
    powers={'Bm1':112,'Jrep':112,'h':1,'rho':1,'delta':2,'i':4,'eta':13,'w':18,'s':31,'transport_quotient':1,'auxiliary_Tf':2}
    mon=tuple(sorted(x for x,n in powers.items() for _ in range(n)))
    need(expected.get(mon)==-32,'uniform nonzero fixed-numeral coefficient')
    naive={v:0 if v in FIXED else 1 for v in child['free']}
    for n,o,a,b in child['source']:
        x=naive[a] if type(a) is str else 0;y=naive[b] if type(b) is str else 0
        naive[n]=x+y if o=='*' else max(x,y)
    need(naive['polynomial']==195,'separate naive upper')
    return {'factor_degrees':degrees,'exact':185,'naive_upper':195,'leading_terms':len(expected),
            'leading_sha256':digest(stable([[list(m),v] for m,v in sorted(expected.items())])),
            'distinguished_coefficient':-32,'distinguished_monomial':powers,'guarded_rows':len(guarded)}

def eval_source(packet,values):
    env=dict(values)
    for n,o,a,b in packet['source']:
        x=env[a] if type(a) is str else a;y=env[b] if type(b) is str else b
        env[n]=x*y if o=='*' else x+y if o=='+' else x-y
    return env

def pell(A,n):
    # Independent logarithmic powering of pairs in Z[sqrt(A^2-1)].
    D=A*A-1
    def product(p,q):return p[0]*q[0]+D*p[1]*q[1],p[0]*q[1]+p[1]*q[0]
    result=(1,0);base=(A,1)
    while n:
        if n&1:result=product(result,base)
        n//=2
        if n:base=product(base,base)
    return result

def sectors():
    count=0;rows=[]
    for Delta in (1,2,3,8):
      for c in (1,3,7,11):
       for R in (1,2,7,12):
        for i in (1,2):
         for epsilon in (-1,1):
          B=Delta*i*i*c**4
          if B<=1:continue
          v=3 if c==1 else 3+4*((epsilon*R-3)*pow(4,-1,c)%c)
          S=i*Delta*c*c;F=B+epsilon
          chi,y=pell(S,v);V,rem=divmod(chi,S)
          need(rem==0 and (V+epsilon*R)%c==0,'odd polynomial quotient congruence')
          U,rem=divmod(V+R*F,c);U+=1
          need(rem==0 and min(F,U,y,V)>0,'positive integral sector witnesses')
          need(v%4==3 and (v-epsilon*R)%c==0,'independent CRT choice')
          actualV=c*(U-1)-R*F;Na=S*S*(actualV*actualV-y*y)+y*y;Ns=Delta*F-S*S
          need(Na==1 and Ns==epsilon*Delta and epsilon*Na*Ns-Delta==0,'complete scalar output zero')
          rows.append([Delta,c,R,i,epsilon,v,F.bit_length(),U.bit_length(),y.bit_length()]);count+=1
    residues=[(s,v,y,(s*s*(v*v-y*y)+y*y)%4) for s in range(4) for v in range(4) for y in range(4)]
    need(all(x[-1]!=3 for x in residues),'Na never minus-one modulo4')
    # Independent odd Chebyshev quotients: constant coefficient of Q_j.
    q0=[1];q1=[-3,4];constants=[]
    for j in range(20):
        q=q0 if j==0 else q1
        need(q[0]==(-1)**j*(2*j+1),'odd quotient constant')
        constants.append(q[0])
        if j:
            nxt=[0]*(len(q1)+1)
            for h,b in enumerate(q1):nxt[h]-=2*b;nxt[h+1]+=4*b
            for h,b in enumerate(q0):nxt[h]-=b
            q0,q1=q1,nxt
    return {'positive_extensions':count,'extension_digest':digest(stable(rows)),'mod4_cases':len(residues),'odd_quotient_constants':constants}

def native(child):
    t=13;p=t*(t+2);n=t*(t+1);R=2*n-1
    X=1<<p;Y=1<<(t+1);E=X*Y;a=Y*(X+1);A=a+2;Delta=A*A-1
    D,c=pell(A,p);tau,k0=pell(2*X*Y*Y+1,n);k=2*k0
    eta=c-k*Y;zeta=k-eta;h,rem=divmod(k-2*n,E)
    need(rem==0 and min(eta,zeta,h)>0,'scaled ratio and retained h')
    gamma,rem=divmod(D-a*c-X,4*a+3)
    need(rem==0 and gamma>1,'main projection')
    need(tau*tau-X*Y*Y*(X*Y*Y+1)*k*k==1 and D*D-Delta*c*c==1,'both exact native norms')
    need(k-h*E-R==1 and c%2==1 and R%4==3 and math.gcd(c,p)==195 and (R-p)%195!=0,'wrong-index CRT separation')
    F=Delta*c**4+1;M=c*D
    need((M-1)**2<F<M*M and F-(M-1)**2==c*(2*D-c) and M*M-F==c*c-1,'strict nonsquare interval')
    # Actual full positive assignment; its packing is deliberately NOT R.
    values={v:1 for v in child['free']}
    values.update(Bm1=15,Kconstant=97,twice_cell_bits=2,inner_bits=1,MC=14,MF=19,
                  w=X//16,s=Y//4096,tau_root=tau,eta=eta,zeta=zeta,h=h,rho=1,sigma=gamma-1)
    env=eval_source(child,values)
    need(env['norm_first']==env['norm_main']==1,'native first/main match actual emitted rows')
    need(env['r_lhs']==61263 and env['norm_index']==-60899 and env['polynomial']!=0,'full-source fixture explicitly nonzero')
    return {'t':t,'p':p,'n':n,'abstract_R':R,'c_bits':c.bit_length(),'F_aux_bits':F.bit_length(),
            'old_CRT_gcd':195,'chosen_auxiliary_index':R,'all_paid_rows_evaluated':82,
            'actual_packing_R':env['r_lhs'],'actual_index_factor':env['norm_index'],
            'full_compiler_zero':False,'large_auxiliary_witnesses_materialized':False}

def verify(root,author_root):
    for ext,pin in AUTHOR.items():need(digest((author_root/(STEM+ext)).read_bytes())==pin,'author pin '+ext)
    for name,pin in PINS.items():need(digest((root/name).read_bytes())==pin,'dependency pin '+name)
    author=json.loads((author_root/(STEM+'.json')).read_text())
    need(author['source_sha256']==AUTHOR['.py'] and author['dependency_pins']==PINS,'author provenance fields')
    parent=json.loads((root/'complete84_scaled_strong_output.json').read_text())['packet'];child=author['packet']
    table,uses=source_graph(parent,child)
    need(author['complete_source_sha256']==digest(stable(child['source'])),'source array fingerprint')
    relation=full_relation(table);degree=uniform_degree(child,table)
    need(child['exact_degree']==185 and child['factor_exact_degrees']==degree['factor_degrees'] and child['universal_soundness']=='UNPROVED','honest degree/theorem metadata')
    rng=random.Random(82184)
    for j in range(32):
        vals={x:(Fraction(rng.randrange(-7,8),rng.randrange(1,6)) if j<16 else rng.randrange(-7,8)) for x in parent['free']}
        old=eval_source(parent,vals)
        vals82={x:old[x] if x in ('L16','auxiliary_Tf') else vals[x] for x in child['free']}
        new=eval_source(child,vals82)
        need(all(new[n]==old[n] for n in table),'whole rational/signed forward map')
    sector=sectors();fixture=native(child)
    return {'status':'PASS','source_sha256':digest(Path(__file__).read_bytes()),'author_pins':dict(AUTHOR),
            'dependency_pins':dict(PINS),'complete_ledger':dict(child['ledger']),'witnesses':18,
            'retained_register_identities':82,'old_coordinate_consumers':uses,'complete_relation':relation,
            'degree':degree,'whole_forward_evaluations':32,'rational_evaluations':16,'retained_value_checks':32*82,
            'sector_checks':sector,'native_fixture':fixture,
            'theorem_scope':'Conditional positive sector: fixed outer tuple and i, Delta>0, c>0 odd, R>0, Delta*i^2*c^4>1. Existence of three positive auxiliary coordinates iff P5 in {-1,1}.',
            'ordinary_input_soundness':'UNPROVED; nonsquare full-parent extension refutes only the literal witness inverse.'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',required=True,type=Path)
    p.add_argument('--author-root',type=Path);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path)
    a=p.parse_args();out=verify(a.root,a.author_root or a.root)
    if a.expect:need(exact(out,json.loads(a.expect.read_text())),'saved receipt differs')
    if a.output:a.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'status':'PASS','operations':82,'degree':out['degree']['exact'],'leading_terms':out['degree']['leading_terms'],'sector_extensions':out['sector_checks']['positive_extensions'],'universal_soundness':'UNPROVED'},sort_keys=True))
if __name__=='__main__':main()
