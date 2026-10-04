#!/usr/bin/env python3
"""Fresh bounded source audit of the current84 upper-ratio deletion.
Predecessor files are authenticated inert data; none are imported or executed.
"""
import argparse, collections, hashlib, json, math
from fractions import Fraction
from pathlib import Path
PINS = {'complete84_scaled_strong_output.py': '8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737', 'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf', 'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade', 'complete75_first_norm_ratio_obstruction.md': '211f00a97780f4b2334e0e44bc4f3b75b5958862b76f816268a228a5128deba3', 'complete80_first_index_deletion_collapse.md': 'a6fb0955f6a19a7564a3070cbf5bdc4e76a6a39a572b46a4d8f656ae9113a575', 'review_complete80_first_index_deletion_collapse.md': 'da03935b4a99d580add0d99f940d7c37c84514138d22e52d40901b7951769b26', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', 'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b'}

def need(ok,msg):
    if not ok: raise RuntimeError(msg)
def sha(b): return hashlib.sha256(b).hexdigest()
def canonical(x): return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def pairs(ps):
    d={}
    for k,v in ps:
        need(k not in d,'duplicate JSON key');d[k]=v
    return d
def readjson(p):
    return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
def same(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
    if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b

def audit(src,free,out):
    known=set(free);names=[];counts=collections.Counter();degrees={x:0 if x in FIXED else 1 for x in free}
    for dst,op,a,b in src:
        need(dst not in known and op in ('+','-','*'),'invalid definition')
        for x in (a,b):need(type(x) is int or isinstance(x,str) and x in known,'unknown operand')
        da=degrees[a] if isinstance(a,str) else 0;db=degrees[b] if isinstance(b,str) else 0
        degrees[dst]=da+db if op=='*' else max(da,db)
        known.add(dst);names.append(dst);counts['M' if op=='*' else 'A']+=1
    live={out}
    for dst,op,a,b in reversed(src):
        if dst in live:
            for x in (a,b):
                if isinstance(x,str):live.add(x)
    need(set(names)<=live and set(free)<=live,'dead row or free port')
    return dict(operations=len(src),multiplications=counts['M'],additions=counts['A'],free_ports=len(free),positive_witnesses=18,all_rows_live=True,all_ports_live=True,gate_degree_upper=degrees[out])

def evaluate(src,values):
    e=dict(values)
    for dst,op,a,b in src:
        av=e[a] if isinstance(a,str) else a; bv=e[b] if isinstance(b,str) else b
        e[dst]=av*bv if op=='*' else av+bv if op=='+' else av-bv
    return e

def pell(a,n,mod=None):
    delta=a*a-1;u,v=1,0;x,y=a,1
    while n:
        if n&1:u,v=u*x+delta*v*y,u*y+v*x
        x,y=x*x+delta*y*y,2*x*y
        if mod:u%=mod;v%=mod;x%=mod;y%=mod
        n//=2
    return u,v
FIXED=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']

def verify(root):
    for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'dependency pin '+n)
    parent=readjson(root/'complete84_scaled_strong_output.json')['packet']
    src=parent['source'];need(len(src)==84,'parent length')
    need(parent['fixed_numerals']==FIXED,'fixed interface')
    need([r for r in src if r[0]=='R10b']==[['R10b','+','eta','zeta']],'actual k sum')
    consumers={x:[r[0] for r in src if x in r[2:]] for x in ('eta','zeta','R10b')}
    need(consumers['zeta']==['R10b'] and consumers['eta']==['R10b','R10a'],'ratio consumers')
    name='first_pell_coefficient'
    child=[[r[0],r[1],*[name if x=='R10b' else x for x in r[2:]]] for r in src if r[0]!='R10b']
    free=[name if x=='zeta' else x for x in parent['free']]
    wit=[name if x=='zeta' else x for x in parent['witnesses']]
    ledger=audit(child,free,parent['output']);need((ledger['operations'],ledger['multiplications'],ledger['additions'])==(83,47,36),'count')
    need(len(wit)==18 and name in wit and 'zeta' not in free,'child interface')
    # Exact whole-source certificate: eta+(k-eta)=k; all remaining rows
    # literally match after replacing the original producer by that cut.
    restored=[r for r in src if r[0]!='R10b']
    need([[r[0],r[1],*[name if x=='R10b' else x for x in r[2:]]] for r in restored]==child,'whole literal reconstruction')
    retained_equalities=0
    for case in range(40):
        e={v:Fraction((case*13+j*7)%19-9,1 if case<20 else (j+case)%5+1) for j,v in enumerate(free)}
        old=dict(e);old['zeta']=e[name]-e['eta'];del old[name]
        p=evaluate(src,old);c=evaluate(child,e)
        need(p['R10b']==e[name],'affine producer')
        for row in child:need(p[row[0]]==c[row[0]],'whole retained register');retained_equalities+=1
        need(p[parent['output']]==c[parent['output']],'whole output')
    main=[]
    for R,Y in [(3,1),(3,2),(7,1),(7,8),(7,64),(11,1),(11,64),(11,512),(15,64),(15,512)]:
        X=2**R;E=X*Y;A=Y*(X+1)+2;Delta=A*A-1;P=2*X*Y*Y+1;n=(R+1)//2
        D,c=pell(A,R);tau,v=pell(P,n);k=2*v;eta=c-k*Y
        need((2*A-1)**2>2*P*X,'exact ratio base bound')
        need(c>k*(Y+1) and eta>k,'upper ratio violation')
        need((k-R-1)%E==0 and k>R+1,'first quotient')
        h=(k-R-1)//E
        need(D*D-Delta*c*c==1 and tau*tau-X*Y*Y*(X*Y*Y+1)*k*k==1,'main first factors')
        need(k-h*E-R==1,'retained index')
        main.append(dict(R=R,Y=Y,n=n,c_bits=c.bit_length(),k_bits=k.bit_length(),eta_positive=True,inverse_zeta_negative=True,h_positive_integer=True))
    auxiliary=[]
    for A in range(3,10):
        R=3;Delta=A*A-1;D,c=pell(A,R);m=2*c*R;f,v=pell(A,m)
        need(v%(c*c)==0,'normalized coefficient integrality');i=v//(c*c);S=Delta*v
        root,y=pell(S,R);need(root%S==0,'odd auxiliary quotient');V=root//S
        numerator=V+c+R*f*f;denominator=c*f
        need(numerator%denominator==0,'literal T integrality');T=numerator//denominator
        need(min(f,i,T,y)>0 and V>0,'auxiliary positivity')
        need(c*(T*f-1)-R*f*f==V,'actual auxiliary argument')
        need(Delta*f*f-S*S==Delta and S*S*(V*V-y*y)+y*y==1,'scaled strong and auxiliary')
        auxiliary.append(dict(A=A,R=R,m=m,c=c,f_bits=f.bit_length(),i_bits=i.bit_length(),T_bits=T.bit_length(),y_bits=y.bit_length(),integers_sha256=sha(canonical([hex(x) for x in (f,i,T,y)]))))
    factorial=[]
    for L in range(4,25):
        t=math.factorial(L);m=t
        while m%2==0:m//=2
        need(pow(2,t,m)==1 % m,'factorial odd-part congruence')
        factorial.append(dict(L=L,odd_part=m,residue=pow(2,t,m)))
    return dict(status='PASS',scope='Literal current84 free-k deletion; full all-input failure proved in companion note; finite examples are components, not complete compiler zeros',dependencies=PINS,
      packet=dict(source=child,free=free,witnesses=wit,fixed_numerals=FIXED,ordinary_input='x',output=parent['output'],factors=parent['factors'],ledger=ledger,exact_degree=187,degree_proof='Invertible homogeneous linear change zeta=k-eta preserves the parent uniform degree',all_ring_identity='F83(k,eta,others)=F84(zeta=k-eta,eta,others)',positive_inverse_condition='k>eta',language_status='all positive inputs on every inherited valid fixed-program slice; refuted candidate'),
      structural=dict(deleted_row=['R10b','+','eta','zeta'],consumers=consumers,retained_literal_rows=83,local_identity='eta+(k-eta)=k',source_sha256=sha(canonical(child))),
      numerical=dict(whole_assignments=40,rational_assignments=20,retained_register_equalities=retained_equalities,main_index_cases=main,auxiliary_cases=auxiliary,factorial_cases=factorial,scope='No full accepting history or compiler-sized Pell tuple is materialized; auxiliary cases are isolated algebraic components'))

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    g=p.add_mutually_exclusive_group();g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args()
    result=verify(a.root.resolve())
    if a.expect:need(same(result,readjson(a.expect)),'typed receipt mismatch')
    if a.output:
        with a.output.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({'status':'PASS','ledger':result['packet']['ledger'],'main_cases':len(result['numerical']['main_index_cases']),'auxiliary_cases':len(result['numerical']['auxiliary_cases'])},sort_keys=True))
if __name__=='__main__':main()
