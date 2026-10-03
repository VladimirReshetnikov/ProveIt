#!/usr/bin/env python3
"""Full exact univariate diagonal expansion modulo 17 of frozen small DAGs.
No R15 rewriting, no degree predictions in arithmetic, no upstream import/exec.
This checker imports only Python's standard library.
"""
import argparse,hashlib,json,struct,time
from pathlib import Path
import sys
sys.dontwritebytecode = True
S=None
PINS={'native_unit_kernel.json': '2d88343037c08fe8b073f67dca531ee73309c0735c1d98a23c20b9ddb1eb08ae', 'native_receipt_fixtures.json': '99e635ffb9a470652aecf3dda2463846b983981dad06a3c69f5e79c8cc0d096c', 'native_backend_small_0.bin': '11f12f4bcda559b4ce05426fcf483115405bb158a0aed6f6d7f060d2b6a31065', 'native_backend_small_0.json': 'ac8e97555686fe84125eb2cb03ce6c5b4f03051d55cc9183e015858ff54842e6', 'native_backend_small_1.bin': '7b00bfaa93c222895d88cbc78b5dd5d80386e415547579e4000abf703c6a1270', 'native_backend_small_1.json': '2309c6ef7246c8611af53d205056d23d8dded7729ee594c030e00cec55518bd4', 'native_backend_small_2.bin': 'edec1cba2d33037880542e5d54859c9db672f9a21e996a1859c93ba4c7a5418c', 'native_backend_small_2.json': '4fb9ece6e59050c6322289ca526185ffd202a50a4788c2ed1403a50d06cf2816', 'native_backend_small_3.bin': '8eaeb2941a66fe712309eda8ceab72d5062032e7d152d1dc1512e41e31e4bca3', 'native_backend_small_3.json': '460f210783b5979b7d5e856ecc45c43cd2bf85c185c4139072bf0fdfdb31f4a7'}
O=Path(__file__).resolve().parent
P=17; B=1<<50

def need(v,msg):
    if not v:raise RuntimeError(msg)
def add(a,b,sign=1):
    q=a.copy()
    for k,v in b.items():
        c=(q.get(k,0)+sign*v)%P
        if c:q[k]=c
        else:q.pop(k,None)
    return q
def mul(a,b):
    q={}
    for i,x in a.items():
        for j,y in b.items():q[i+j]=q.get(i+j,0)+x*y
    return {k:v%P for k,v in q.items() if v%P}
def op(code,a,b):return add(a,b) if code==0 else add(a,b,-1) if code==1 else mul(a,b)
def cn(v):return {0:v%P} if v%P else {}
def raw(meta,blob,xdegree):
    cs=[]
    for row in meta['constants']:
        need(row[0]=='int','Unexpected small fixture recipe');cs.append(cn(int(row[1])))
    vals=[]
    def get(h):return cs[-h-1] if h<0 else {xdegree if h==B else 1:1} if h>=B else vals[h]
    for code,a,b in struct.iter_unpack('<Bqq',blob[8:]):vals.append(op(code,get(a),get(b)))
    return vals[meta['output']]
def packet(pkt,xdegree):
    env={x:{xdegree if x=='x' else 1:1} for x in pkt['parameters']+pkt['auxiliaries']}
    def get(v):return cn(v) if type(v)is int else env[v]
    for name,code,a,b in pkt['source']:env[name]=op({'+':0,'-':1,'*':2}[code],get(a),get(b))
    total=cn(1)
    for a,b in pkt['comparisons'][:-1]:
        r=add(get(a),get(b),-1);total=add(total,mul(r,r))
    return add(mul(env[pkt['unit_register']],total),cn(1),-1)
class Poly:
    def __init__(self,v):self.v=v if isinstance(v,dict) else cn(v)
    @staticmethod
    def wrap(v):return v if isinstance(v,Poly) else Poly(v)
    def __add__(self,v):return Poly(add(self.v,self.wrap(v).v))
    __radd__=__add__
    def __neg__(self):return Poly({k:-v%P for k,v in self.v.items()})
    def __sub__(self,v):return self+-self.wrap(v)
    def __rsub__(self,v):return self.wrap(v)+-self
    def __mul__(self,v):return Poly(mul(self.v,self.wrap(v).v))
    __rmul__=__mul__
    def __pow__(self,n):
        v=Poly(1);b=self
        while n:
            if n&1:v=v*b
            n//=2
            if n:b=b*b
        return v

def generated_formula(program,kernel):
    # Direct polynomial formulas, with no special cancellation rule.
    m=len(program);s=2*m;groups=list(dict.fromkeys(program));g=len(groups);N=s+g+5
    t=Poly({1:1});P0=2*t;Uf=P0*t+t;D=Uf+2*t
    ke=max(3,(s+3).bit_length(),2*max(groups)+2);K=pow(2,ke,P)
    Bv=K*D;J=s*t-s;p=(Bv-1)*J+1
    powers=[p**i for i in range(N+1)]
    def pack(seq):return sum((a*powers[i] for i,a in enumerate(seq)),Poly(0))
    def rep(n):return sum(powers[:n],Poly(0))
    selected=[program.count(a)*(t-1) for a in groups];zs=[t-1]*g
    nextU=2*t+sum(selected,Poly(0));nextV=t
    for a,q,z in zip(groups,selected,zs):
        nextV+=(pow(2,2*a+1,P)-1)*z
        if a:nextV+=2*((pow(4,a,3*P)-1)//3)*q
    res=[(3+g)*t-p,Bv*nextU+1-(t+p*Uf),Bv*nextV+1-(t+p*t)]
    res += [t-1 if m==1 else 2*m*t-(Bv-1)*(m*(m-1)*(t-1))+t-(J+3*m)]
    S=pack([t]*s)-rep(s);Mc=J*rep(s);T=t+p*t;G=pack(selected);Hb=t*rep(g);Mb=(Bv-1)*G;Zb=pack(zs);RM=(D-1)*J*(1+p)
    common=powers[g]*S+powers[g+s]*T
    ports={'H':Hb+common+powers[g+s+2]*Bv+powers[g+s+4]*P0,
           'M':Mb+powers[g]*Mc+powers[g+s]*RM+powers[g+s+2]*(Bv-1)+powers[g+s+4]*(P0-1),
           'Z':Zb+common,'scale':powers[N]}
    e={x:t for x in kernel['auxiliaries']};e.update({'@'+k:v for k,v in ports.items()})
    def r(v):return Poly(v) if type(v)is int else e[v]
    for name,code,a,b in kernel['source']:
        aa,bb=r(a),r(b);e[name]=aa+bb if code=='+' else aa-bb if code=='-' else aa*bb
    res.extend(r(a)-r(b) for a,b in kernel['comparisons'])
    F=e[kernel['unit']]*(1+sum((a*a for a in res),Poly(0)))-1
    expected=87*N+16
    need(max(F.v)==expected,'Generated full diagonal expansion degree mismatch')
    expected_c=-pow(2,148,P)*pow(pow(2,ke+1,P)*s%P,29*N-8,P)%P
    need(F.v[expected]==expected_c,'Generated full expansion coefficient mismatch')
    return {'program':program,'m':m,'g':g,'N':N,'modulus':P,'degree':max(F.v),'leading_coefficient':F.v[max(F.v)],'nonzero_terms':len(F.v),'R15_rewrite_used':False}

def main():
    global S
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--source-dir',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();S=args.source_dir.resolve()
    for name,pin in PINS.items():need(hashlib.sha256((S/name).read_bytes()).hexdigest()==pin,'Frozen input pin mismatch: '+name)
    t=time.monotonic();fixtures=json.loads((S/'native_receipt_fixtures.json').read_text())['fixtures'];rows=[]
    for idx,fixture in enumerate(fixtures):
        meta=json.loads((S/f'native_backend_small_{idx}.json').read_text());blob=(S/f'native_backend_small_{idx}.bin').read_bytes()
        need(hashlib.sha256(blob).hexdigest()==meta['source_sha256'],'Raw source pin mismatch')
        for xd in ((1,2) if idx==0 else (1,)):
            a=raw(meta,blob,xd);b=packet(fixture['packet'],xd)
            need(a==b,'Entire diagonal polynomial disagreement')
            m=len(fixture['program']);N=2*m+len(set(fixture['program']))+5;expected=(xd+2)*(29*N-8)+40
            need(max(a)==expected,'Diagonal degree disagreement')
            row={'fixture':idx,'program':fixture['program'],'X_diagonal_power':xd,'modulus':P,'degree':max(a),'leading_coefficient':a[max(a)],'nonzero_terms':len(a),'all_coefficients_equal_to_pinned_receipt':True,'coefficients':[[k,a[k]] for k in sorted(a)]}
            rows.append(row);print(json.dumps({k:v for k,v in row.items() if k!='coefficients'}),flush=True)
    kernel=json.loads((S/'native_unit_kernel.json').read_text())
    generic=[generated_formula(p,kernel) for p in ([0,0],[0,0,0],[0]*5,[2**32-1],[0,2**32-1])]
    for row in generic:print(json.dumps(row),flush=True)
    record={'generated_formula_cases':generic,'status':'PASS','upstream_executed':False,'R15_identity_rewrite_used':False,'modulus':P,'cases':rows,'seconds':time.monotonic()-t}
    args.output.write_text(json.dumps(record,indent=2)+'\n')
if __name__=='__main__':main()
