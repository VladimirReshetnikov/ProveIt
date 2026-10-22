"""Independently authored root12 circuit generator; upstream JSON is inert input."""
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent

class Circuit:
    def __init__(self, prefix):
        self.source=list(prefix)
        self.cache={}
        for name,op,a,b in self.source:
            self.cache[self.key(op,a,b)]=name
    @staticmethod
    def key(op,a,b):
        if op in ('+','*') and str(a)>str(b):a,b=b,a
        return op,a,b
    def op(self, op, a, b, name=None):
        key=self.key(op,a,b)
        if key in self.cache:return self.cache[key]
        name=name or 'r12_'+str(len(self.source)+1)
        self.source.append([name,op,a,b]);self.cache[key]=name
        return name
    def mul(self,a,b,name=None):return self.op('*',a,b,name)
    def add(self,a,b,name=None):return self.op('+',a,b,name)
    def sub(self,a,b,name=None):return self.op('-',a,b,name)
    def sq(self,a,name=None):return self.mul(a,a,name)

def build(scaled_y=False,free_i=False):
    src=json.loads((HERE/'upstream/arithmetic/amalgam14_system67.json').read_text())
    prefix=[]
    for row in src['source']:
        if row[0]=='f2':break
        if row[0] not in {'gammaH','D','D2','N1'}:prefix.append(row)
    c=Circuit(prefix);mul,add,sub,sq=c.mul,c.add,c.sub,c.sq
    A=add('first_product',1,'Afirst')
    G=add('Dc2',1,'Gmain')
    ii='i' if scaled_y or free_i else mul('H','j','i')
    I=mul(ii,'c2','Istrong');S=mul('Delta',I,'Saux')
    Q=sq(S,'Qaux');Dm=mul(I,S,'Dstrongm1');D=add(Dm,1,'Dstrong')
    d=sub(Q,1,'daux')
    v=mul('c','T','vaux');v2=sq(v)
    b=add('c',mul('R',D),'baux')
    Db=add(mul(D,v2),sq(b),'Dv2plusb2')
    e=sub(mul(Q,Db),1,'eaux')
    B=mul(2,mul(Q,mul(v,b)),'Baux')
    # |f'|=sqrt(D)<S and Q/(Q-1)<=2 give |y'|<2*(S*v+b).
    Yb=mul(2,add(mul(S,v),b),'Ybound')
    if scaled_y:
        Yb=mul(d,Yb,'Rbound')
        e=mul(d,e,'eraux')
        B=mul(d,B,'Braux')
    Pweight=mul('H',Yb,'Pweight')
    K=add(Pweight,1,'Kweight')
    Z=add(mul('H','t'),mul(K,'Dbase'),'Zlinear')
    u=mul(6,Pweight,'uweight');H2=sq('H','H2')
    # P = a - bb*r - cc*s + ee*r*s, r^2=A, s^2=G.
    araw=add(add(sq(Z),mul(sq(u),A)),mul(sq(K),G))
    a=sub(araw if scaled_y else mul(d,araw),mul(H2,e),'P00')
    twice_d=2 if scaled_y else mul(2,d)
    bb=mul(twice_d,mul(Z,u),'P10abs')
    cc=mul(twice_d,mul(Z,K),'P01abs')
    ee=mul(twice_d,mul(u,K),'P11')
    ell=mul(sq(H2),mul(sq(B),D),'Lnorm')
    # F=P^2-Lnorm. Store positive magnitudes of the two negative coefficients.
    f0=sub(add(add(sq(a),mul(A,sq(bb))),mul(G,add(sq(cc),mul(A,sq(ee))))),ell,'F00')
    fb=mul(2,add(mul(a,bb),mul(G,mul(cc,ee))),'F10abs')
    fc=mul(2,add(mul(a,cc),mul(A,mul(bb,ee))),'F01abs')
    fe=mul(2,add(mul(a,ee),mul(bb,cc)),'F11')
    # Norm first in s and then in r.
    n0=sub(add(sq(f0),mul(A,sq(fb))),mul(G,add(sq(fc),mul(A,sq(fe)))),'N00')
    n1=mul(2,sub(mul(G,mul(fc,fe)),mul(f0,fb)),'N10')
    res=sub(sq(n0),mul(A,sq(n1)),'Res12')
    system_source=list(c.source)
    unit=add(res,1,'unit12')
    out=sub(mul(mul('Nk','Nt'),unit),1,'polynomial12')
    witnesses=['J','F','alpha','z','h','i' if scaled_y or free_i else 'j','T','s','w','eta','zeta','t']
    binding=json.loads((HERE/'COEFFICIENT_BINDING.json').read_text())
    base={'coefficient_binding':binding,
          'fixed_numerals':['beta','K0','MC','MF'],'witnesses':witnesses,
          'domain':'strictly positive integers',
          'proof':'ROOT12_SATURATED_PROOF.md' if free_i else 'ROOT12_PROOF.md','provenance':'Independently authored new circuit; no received program executed.'}
    stem='root12_saturated' if free_i else 'root12_scaled_y' if scaled_y else 'root12'
    for name,source,extra in [
        (stem+'_system',system_source,{'comparisons':[['Nk',1],['Nt',1],[res,0]]}),
        (stem+'_product',c.source,{'output':out})]:
        data=dict(base,name=name,source=source,**extra)
        data['ledger']={'operations':len(source),'multiplications':sum(row[1]=='*' for row in source),
                        'additions_subtractions':sum(row[1]!='*' for row in source)}
        (HERE/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
        print(name,data['ledger'])

if __name__=='__main__':
    build();build(True);build(free_i=True)
