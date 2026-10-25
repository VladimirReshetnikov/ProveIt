#!/usr/bin/env python3
"""Exact circuit identities and complete leading forms; no third-party modules."""
from pathlib import Path
from collections import Counter
from functools import reduce
import gzip, hashlib, json, random

ROOT = Path(__file__).resolve().parent

class Poly:
    def __init__(self, x=0):
        self.d = x if isinstance(x, dict) else ({} if x == 0 else {(): x})
    @staticmethod
    def v(name):
        return Poly({((name, 1),): 1})
    def __add__(self, other):
        other = aspoly(other)
        d = dict(self.d)
        for m, c in other.d.items():
            d[m] = d.get(m, 0) + c
            if not d[m]: del d[m]
        return Poly(d)
    __radd__ = __add__
    def __neg__(self): return Poly({m:-c for m,c in self.d.items()})
    def __sub__(self, other): return self + -aspoly(other)
    def __rsub__(self, other): return aspoly(other) + -self
    def __mul__(self, other):
        other=aspoly(other); d={}
        for m,c in self.d.items():
            for n,e in other.d.items():
                powers=dict(m)
                for v,k in n: powers[v]=powers.get(v,0)+k
                z=tuple(sorted(powers.items()))
                d[z]=d.get(z,0)+c*e
                if not d[z]: del d[z]
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        if n < 0: raise ValueError("negative exponent")
        ans=Poly(1); x=self
        while n:
            if n&1: ans=ans*x
            x=x*x; n//=2
        return ans
    def __eq__(self,other): return self.d==aspoly(other).d
    def serial(self): return [{"powers":dict(m),"coefficient":c} for m,c in sorted(self.d.items())]

def aspoly(x): return x if isinstance(x,Poly) else Poly(x)
def require(test,message):
    if not test: raise ValueError(message)

def topology(g):
    names=set(g['witnesses'])|set(g['fixed_numerals']); rows=g['source']
    for name,op,a,b in rows:
        require(name not in names, 'duplicate gate '+name)
        require(op in ('+','-','*'),'nonbinary arithmetic gate')
        for x in (a,b): require(isinstance(x,int) or x in names,'undefined operand '+str(x))
        names.add(name)
    dependencies={r[0]:r[2:] for r in rows}; live=set()
    def visit(x):
        if isinstance(x,int) or x in live: return
        live.add(x)
        if x in dependencies:
            for t in dependencies[x]: visit(t)
    visit(g['output'])
    require(live==names,'dead gate, input or port')
    return Counter(row[1] for row in rows)

def exact_cuts(g):
    defs={r[0]:r[1:] for r in g['source']}
    boundary={n:Poly.v(n) for n in g['witnesses']+g['fixed_numerals']}
    used=set(); receipts=[]
    def expand(name,memo):
        if isinstance(name,int): return Poly(name)
        if name in boundary:return boundary[name]
        if name in memo:return memo[name]
        op,a,b=defs[name]; used.add(name)
        p,q=expand(a,memo),expand(b,memo)
        ans={'+':lambda:p+q,'-':lambda:p-q,'*':lambda:p*q}[op]()
        memo[name]=ans;return ans
    def sym(n): return boundary[n]
    def cut(name,expected):
        got=expand(name,{})
        require(got==expected,'exact polynomial cut mismatch: '+name)
        receipts.append({'register':name,'collected_terms':len(got.d)})
        boundary[name]=Poly.v(name)
    p=sym
    cut('bJ',p('beta')*p('J'))
    cut('q',p('bJ')+1)
    cut('q2',p('q')**2)
    if g['denominator']=='q4':cut('q4',p('q2')**2)
    cut('q3',p('q2')*p('q'))
    cut('Y',p('q3')*p('s'))
    cut('qmF',p('q')-p('F'))
    cut('C',p('qmF')-p('alpha'))
    cut('X',p('w')*p('q'))
    cut('k',p('eta')+p('zeta'))
    cut('c',p('k')*p('Y')+p('eta'))
    cut('XY',p('X')*p('Y'))
    cut('Am1',p('XY')+p('Y'))
    cut('Hp',4*p('Am1')-1)
    cut('Ap1',p('Am1')+2)
    v0=p('XY')*p('Y')
    cut('Dtau',1+v0*(v0+1)*p('k')**2)
    cut('R',(p('bJ')*p('qmF')+p('alpha'))*(p('q2')-1)+(p('MC')+p('q')*p('MF'))*p('J'))
    cut('e',p('k')-p('R')-1)
    cut('Bt',(p('K0')+p('w'))*p('C')-p('F'))
    cut('U',p('i')*p('c')**2)
    cut('Delta',p('Am1')*p('Ap1'))
    cut('DpI2',p('Delta')*p('U')**2*p('Dtau'))
    cut('Df',1+p('DpI2'))
    cut('Fsqr',1+4*p('DpI2')*p('Df'))
    cut('Q',4*p('Delta')*p('DpI2')*p('Df'))
    cut('cTR',p('c')*p('T')-p('R'))
    cut('V',p('Fsqr')*p('cTR')-p('c'))
    cut('V2',p('V')**2)
    cut('Kpos',p('X')*(3*p('c')-2*p('X'))+2)
    den=p(g['denominator'])
    weight=p('V2') if g['transport_weight']=='V2' else p('cTR')*p('V')
    cut('Znum',p('bJ')*den*(p('Hp')*(p('n')-weight*p('Bt'))+p('Kpos'))-p('Hp')*(den*p('Bt')+p('bJ')*p('e')))
    cut('Mtot',p('bJ')*den*p('Hp'))
    cut('Dg',p('Dtau')*p('Df'))
    rg=p('Mtot')**2*p('Dg')
    cut('N',p('Q')*(p('Znum')**2-rg*p('V2'))+rg-p('Znum')**2)
    require(used==set(defs),'uncovered gates: '+repr(set(defs)-used))
    return receipts

def leading(g):
    env={v:(1,Poly.v(v)) for v in g['witnesses']}
    env.update({v:(0,Poly.v(v)) for v in g['fixed_numerals']})
    records=[]
    def value(v):return (0,Poly(v)) if isinstance(v,int) else env[v]
    for name,op,a,b in g['source']:
        da,pa=value(a);db,pb=value(b)
        if op=='*':d,top=da+db,pa*pb
        elif da>db:d,top=da,pa
        elif db>da:d,top=db,pb if op=='+' else -pb
        else:d,top=da,pa+pb if op=='+' else pa-pb
        require(bool(top.d),'leading cancellation requiring deeper analysis: '+name)
        env[name]=d,top;records.append({'register':name,'degree':d,'top_terms':len(top.d)})
    q0=Poly.v('beta')*Poly.v('J');k0=Poly.v('eta')+Poly.v('zeta')
    w,s,i,T,F,alpha=(Poly.v(v) for v in ('w','s','i','T','F','alpha'))
    xy=g['denominator']=='XY'
    if g['transport_weight']=='V2':
        expected=2**14*q0**378*w**(48 if xy else 46)*s**(110 if xy else 108)*i**20*k0**64*T**4*(q0-F-alpha)**2
    else:
        expected=-(2**10)*q0**284*w**(36 if xy else 34)*s**(82 if xy else 80)*i**14*k0**46*T**2
    degree,top=env[g['output']]
    require(degree==g['exact_degree'],'degree header')
    require(top==expected,'entire highest homogeneous polynomial')
    return {'degree':degree,'highest_homogeneous_terms':top.serial(),'registers':records}

def binding(g):
    vals={};receipts=[]
    for name,item in g['coefficient_binding']['ports'].items():
        path=ROOT/g['coefficient_binding']['path']/item['file'];blob=path.read_bytes();raw=gzip.decompress(blob)
        require(hashlib.sha256(blob).hexdigest()==item['gzip_sha256'],'compressed coefficient '+name)
        require(hashlib.sha256(raw).hexdigest()==item['raw_sha256'],'coefficient bytes '+name)
        vals[name]=int.from_bytes(raw,'little')
        require(vals[name].bit_length()==item['bits'],'coefficient bit length '+name)
        receipts.append({'port':name,'raw_sha256':item['raw_sha256'],'bits':item['bits']})
    require(vals['beta']>=31 and vals['beta']%2==1 and vals['K0']>0 and 0<vals['MC']<vals['beta']<vals['MF']<2*vals['beta'],'four-port box')
    return receipts

def identities():
    a,d,u,e,b,c,z,m,g,q,v=(Poly.v(v) for v in ('a','Delta','U','E','b','c','Z','M','G','Q','V'))
    require(1+4*a*(1+a)==(1+2*a)**2,'Pell doubling identity')
    aa=d*u*u*e;gg=e*(1+aa)
    require(d*(4*aa*(1+aa))==4*d*d*u*u*gg,'automatic divisibility identity')
    require(q*(z*z-m*m*g*v*v)+(m*m*g-z*z)==(q-1)*z*z-m*m*g*(q*v*v-1),'finalizer identity')
    # Denominator certificate identities at X=wq,Y=sq^3.
    w,qq,s=(Poly.v(v) for v in ('w','q','s'))
    x,y=w*qq,s*qq**3
    require(x*y==qq**4*(w*s),'q^4 divides XY')
    require(4*x*y*y==(x*y)*(4*y),'XY divides first-index modulus')
    require(4*x*y*y==qq**4*(4*w*s*s*qq**3),'q^4 divides first-index modulus')
    return 6

def main():
    result={'exact_general_identities':identities(),'circuits':[],'interpretation':'Finite polynomial verification; the unbounded number-theoretic equivalence is in PROOF.md.'}
    for name in ('equation_XY_V2.json','equation_XY_bV.json','equation_q4_V2.json','equation_q4_bV.json'):
        path=ROOT/name;g=json.loads(path.read_text());ops=topology(g)
        require(sum(ops.values())==g['operations'],'operation count')
        require(dict(ops)==g['operation_breakdown'],'operation breakdown')
        cuts=exact_cuts(g);high=leading(g);coeff=binding(g)
        result['circuits'].append({'file':name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'operations':sum(ops.values()),'breakdown':dict(ops),'cuts':cuts,'leading':high,'coefficients':coeff})
    (ROOT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'general_identities':result['exact_general_identities'],'circuits':[{'file':r['file'],'operations':r['operations'],'degree':r['leading']['degree'],'exact_cuts':len(r['cuts']),'highest_terms':len(r['leading']['highest_homogeneous_terms'])} for r in result['circuits']]},indent=2))

if __name__=='__main__':main()
