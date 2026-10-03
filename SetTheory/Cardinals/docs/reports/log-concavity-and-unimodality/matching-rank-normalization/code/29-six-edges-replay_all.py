"""Exact rational reconstruction of the three six-edge first-gap certificates.

This uses only the Python standard library and does not import any discovery
script, optimizer, symbolic algebra system, or stored expanded target.
"""
from fractions import Fraction
from itertools import combinations_with_replacement
from pathlib import Path
import json

class P:
    def __init__(self, value=0):
        self.a=dict(value) if isinstance(value,dict) else ({(0,)*7:Fraction(value)} if value else {})
    @staticmethod
    def coerce(x):return x if isinstance(x,P) else P(x)
    def __add__(self,other):
        out=dict(self.a)
        for m,c in self.coerce(other).a.items():out[m]=out.get(m,0)+c
        return P({m:c for m,c in out.items() if c})
    __radd__=__add__
    def __neg__(self):return P({m:-c for m,c in self.a.items()})
    def __sub__(self,other):return self+-self.coerce(other)
    def __rsub__(self,other):return self.coerce(other)+-self
    def __mul__(self,other):
        out={}
        for a,x in self.a.items():
            for b,y in self.coerce(other).a.items():
                m=tuple(i+j for i,j in zip(a,b));out[m]=out.get(m,0)+x*y
        return P({m:c for m,c in out.items() if c})
    __rmul__=__mul__
    def __truediv__(self,value):return self*Fraction(1,value)
    def __pow__(self,k):
        if type(k)!=int or k<0:raise ValueError('invalid exponent')
        out=P(1)
        for _ in range(k):out=out*self
        return out
    def __eq__(self,other):return self.a==self.coerce(other).a

def variables():
    out=[]
    for i in range(7):
        m=[0]*7;m[i]=1;out.append(P({tuple(m):Fraction(1)}))
    return out

def rank(a,b):return any(a>>i&1 and b>>j&1 for i in range(3) for j in range(3) if i!=j)
def pairs(a,b):return sum(rank(a&m,b&m) for m in [3,5,6])
def triple(a,b,c):
    return int(any(a>>i&1 and b>>j&1 and c>>k&1 for i in range(3) for j in range(3) for k in range(3) if len({i,j,k})==3))

def setup(name):
    n,p,q,d,g,e,f=variables()
    u=p-d;v=d-g;mu=n-e;m=n-f;hp=p-g
    X=2*p*p-3*n*q;H=4*p*u*mu-2*n*u*u-3*q*mu*mu
    if name=='triangular':
        gs=[n-4,p-2*n+3,q-n+2,3*q-2*p,e,mu-3,u-mu,d-e*mu,q-e*u,q+e*u-2*d,
            n*(n-1)-e*(e-1)-2*p,mu*(mu-1)-2*u,H,X-2*d*d+4*e*q,
            mu*(mu-1)*(mu-2)+6*e*u-6*q,
            f-e,m-2,g-e*(f-e),f*(f-1)-e*(e-1)-2*g,
            hp-f*m,2*f*m+m*(m-1)-2*hp,q-m*g,
            6*m*g+3*f*m*(m-1)+m*(m-1)*(m-2)-6*q,
            2*f*p*p-3*f*n*q-2*n*g*g,2*hp*hp-3*q*m,
            v-e*m,e*m+m*(m-1)/2-v,2*u*(2*hp-u)-3*q*m,
            X,2*p*p*(n-2)-3*n*(n-1)*q,n*(n-1)*(n-2)-6*q,hp-n+1,g,v]
        c0=q+3*p-d-g+3*n-f-e+1
        def kap(a):return q*a.bit_count()+u*(2 if a.bit_count()==1 else 3)+v*pairs(3,a)+g*pairs(1,a)+(n-f)+(f-e)*int(bool(a&6))+e*int(bool(a&4))
        def lam(a,b):return q*pairs(a,b)+u+v*triple(3,a,b)+g*triple(1,a,b)
        names=['n','p','q','d','g','e','f']
    elif name=='star_edge':
        gs=[d,u,mu,n,p,q,n-f,p-g,n-e-f,n-4,p-2*n+3,q-n+2,3*q-2*p,e,mu-3,u-mu,d-e*mu,q-e*u,q+e*u-2*d,
            n*(n-1)-e*(e-1)-2*p,mu*(mu-1)-2*u,H,X-2*d*d+4*e*q,
            mu*(mu-1)*(mu-2)+6*e*u-6*q,
            f,mu-f,m-2,g,f*(f-1)-2*g,hp-f*m,2*f*m+m*(m-1)-e*(e-1)-2*hp,q-m*g,
            6*m*g+3*f*m*(m-1)+m*(m-1)*(m-2)-6*q,
            2*f*p*p-3*f*n*q-2*n*g*g,2*hp*hp-3*q*m,p-d-g,2*(p*p-d*d-g*g)-3*q*mu,
            p-g-e*mu-f*(mu-f),q-e*u-(mu-f)*g,
            6*e*u+6*(mu-f)*g+3*f*(mu-f)*(mu-f-1)+(mu-f)*(mu-f-1)*(mu-f-2)-6*q,
            u-2*mu+4,hp-2*n+4,X,2*p*p*(n-2)-3*n*(n-1)*q,n*(n-1)*(n-2)-6*q,hp-n+1]
        c0=q+3*p-d-g+3*n-2*e+1
        def kap(a):return q*a.bit_count()+(p-d-g)*(2 if a.bit_count()==1 else 3)+d*pairs(3,a)+g*pairs(5,a)+(n-e)+e*int(bool(a&4))
        def lam(a,b):return q*pairs(a,b)+(p-d-g)+d*triple(3,a,b)+g*triple(5,a,b)
        names=['n','p','q','d','g','e','f']
    elif name=='transpose':
        n,p,q,g1,g2,f1,f2=variables()
        gs=[n-4,p-2*n+3,q-n+2,3*q-2*p,2*p*p-3*n*q,n*(n-1)-2*p,
            2*p*p*(n-2)-3*n*(n-1)*q,n*(n-1)*(n-2)-6*q,p-g1-g2,2*(p*p-g1*g1-g2*g2)-3*n*q]
        for f,g in [(f1,g1),(f2,g2)]:
            m=n-f;h=p-g
            gs.extend([f,m-2,g,f*(f-1)-2*g,h-f*m,2*f*m+m*(m-1)-2*h,q-m*g,
                       6*m*g+3*f*m*(m-1)+m*(m-1)*(m-2)-6*q,
                       2*f*p*p-3*f*n*q-2*n*g*g,2*h*h-3*q*m,h-n+1])
        c0=q+3*p-g1-2*g2+3*n-f2+1
        def kap(a):return q*a.bit_count()+(p-g1-g2)*(2 if a.bit_count()==1 else 3)+g1*pairs(6,a)+g2*pairs(1,a)+(n-f2)+f2*int(bool(a&6))
        def lam(a,b):return q*pairs(a,b)+(p-g1-g2)+g1*triple(6,a,b)+g2*triple(1,a,b)
        names=['n','p','q','g1','g2','f1','f2']
    else:raise ValueError(name)
    return n,gs,c0,kap,lam,names

def run():
    root=Path(__file__).resolve().parent.parent/'data'
    records={}
    files={'triangular':'find_triangular_first.json','star_edge':'find_star_edge_first.json','transpose':'find_transpose_first.json'}
    expected={(a,b) for a,b in combinations_with_replacement(range(1,8),2) if rank(a,b)}
    for name,fn in files.items():
        data=json.loads((root/fn).read_text());n,gs,c0,kap,lam,names=setup(name)
        if data['variables']!=names:raise RuntimeError(('variable order',name))
        if len(data['generators'])!=len(gs):raise RuntimeError(('generator count',name))
        seen=set();count=0;cache={}
        for item in data['certificates']:
            pair=tuple(item['masks'])
            if pair in seen:raise RuntimeError(('duplicate profile',name,pair))
            seen.add(pair);a,b=pair
            target=(n-2)*(16*kap(a)*kap(b)-15*c0*lam(a,b))
            if item['margin']!=1:raise RuntimeError(('strict remainder',name))
            rebuilt=P(1)
            for term in item['terms']:
                powers=tuple(term['powers']);weight=Fraction(term['weight'])
                if len(powers)!=len(gs) or any(type(k)!=int or k<0 for k in powers) or weight<=0:raise RuntimeError('invalid term')
                if powers not in cache:
                    value=P(1)
                    for g,k in zip(gs,powers):value=value*g**k
                    cache[powers]=value
                rebuilt=rebuilt+weight*cache[powers];count+=1
            if rebuilt!=target:raise RuntimeError(('identity mismatch',name,pair))
        if seen!=expected:raise RuntimeError(('coverage mismatch',name,seen^expected))
        records[name]={'identities':len(seen),'positive_terms':count,'generators':len(gs),'all_exact':True}
    records['total_identities']=sum(v['identities'] for v in records.values())
    records['total_positive_terms']=sum(v['positive_terms'] for v in records.values() if isinstance(v,dict))
    return records

if __name__=='__main__':
    r=run();Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
