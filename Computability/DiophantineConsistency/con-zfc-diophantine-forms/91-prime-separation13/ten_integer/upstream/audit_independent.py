#!/usr/bin/env python3
"""Independent SymPy audit of root's ten-integer triangular shears."""
from pathlib import Path
from functools import lru_cache
import gzip,hashlib,json
import sympy as s

ROOT=Path(__file__).resolve().parent
OUT=Path(__file__).resolve().parent/'INDEPENDENT_AUDIT.json'
def need(c,m):
    if not c:raise RuntimeError(m)
def load(f):return json.loads((ROOT/f).read_text())

def expression(body,cuts):
    @lru_cache(None)
    def at(i):
        if i in cuts:return cuts[i]
        n=body['nodes'][i]; k=n['kind']
        if k=='literal':return s.Integer(n['value'])
        if k in ['variable','fixed']:return s.Symbol(n['name'])
        a,b=at(n['left']),at(n['right'])
        if k=='add':return a+b
        if k=='sub':return a-b
        if k=='mul':return a*b
        raise RuntimeError(k)
    return at

def heads(body,prime,values):
    deg=[];coeff=[]
    for n in body['nodes']:
        k=n['kind']
        if k=='variable':d,c=1,1
        elif k=='fixed':d,c=0,values[n['name']]
        elif k=='literal':d,c=0,n['value']
        else:
            i,j=n['left'],n['right']
            if k=='mul':d,c=deg[i]+deg[j],coeff[i]*coeff[j]
            else:
                d=max(deg[i],deg[j]); a=coeff[i] if deg[i]==d else 0;b=coeff[j] if deg[j]==d else 0
                c=a+b if k=='add' else a-b
        deg.append(d);coeff.append(c%prime)
    return deg,coeff

def main():
    old=load('upstream/integer10.json')
    manifest=load('FIXED_COEFFICIENTS.json');vals={}
    for n,r in manifest.items():
        raw=gzip.decompress((ROOT/r['file']).read_bytes());need(hashlib.sha256(raw).hexdigest()==r['raw_sha256'],'fixed '+n)
        vals[n]=(-1 if raw[0] else 1)*int.from_bytes(raw[1:],'little')
    dg,lc=heads(old,1000003,vals)
    observed={n:dg[old['named_nodes'][n]] for n in ['halfA','B1','C','xi','Sigma','Theta','guard','lucas']}
    expect={'halfA':16384,'B1':7942,'C':1,'xi':2,'Sigma':81922,'Theta':81925,'guard':294619,'lucas':458818}
    need(observed==expect,'actual prefix degree binding')
    need(all(lc[old['named_nodes'][n]]!=0 for n in expect),'prefix highest coefficient attained')
    h,B,C,xi,y=s.symbols('h B C xi y')
    names=['halfA','B1','C','xi']; symbols=[h,B,C,xi]
    def cuts_for(body):
        cuts={body['named_nodes'][n]:v for n,v in zip(names,symbols)}
        for i,n in enumerate(body['nodes']):
            if n['kind']=='variable' and n['name']=='y':cuts[i]=y
        return cuts
    A=2*h;u=C*C;D=(A*A-4)*u+4;E0=u*xi;E=u*D*xi
    F=4*(A*A-4)*u*u*D*xi*xi+1
    G=(h-1)*(F-1)-1;H=C+F*(B-C+16*E*y)
    I=(G*G-1)*H*H+1;a1=D*F*I
    at=expression(old,cuts_for(old))
    for n,value in [('D',D),('E0',E0),('E',E),('F',F),('G',G),('H',H),('I',I),('lucas',a1)]:
        need(s.expand(at(old['named_nodes'][n])-value)==0,'actual literal register '+n)
    P0=2*A*E;P1=2*A*E0*(D-2*u)
    need(s.expand(D*F-P0**2-(D-16*E**2))==0,'linear defect')
    need(s.expand(D*F-P1**2-(D+16*E0**2*(u*(3*u-4)*A*A-16*(u-1)**2)))==0,'cubic defect')
    T=xi*(B-C)*(u*(2*h*h-11)+6)+16*u*xi*xi*y*(u*u*(8*h**4-52*h*h+143)+u*(32*h*h-176)+48)+3*y
    R6=32768*u**7*xi**4*h**9*((h-1)*T-2*y)
    roots={'linear':P0*G*H,'cubic':P1*G*H,'sixterm':R6}
    weights=[16384,7942,1,2,1]
    ans={}
    for variant,R in roots.items():
        b=load('integer10_'+variant+'.json')
        at=expression(b,cuts_for(b))
        need(s.expand(at(b['named_nodes']['shear'])-R)==0,'literal shear '+variant)
        rp=s.Poly(s.expand(R),h,B,C,xi,y)
        df=s.Poly(s.expand(a1-R*R),h,B,C,xi,y)
        wd=lambda p:max(sum(a*w for a,w in zip(m,weights)) for m,c in p.terms())
        rd,dd=wd(rp),wd(df)
        # m is absent from every ancestral node of the shear register.
        todo=[b['named_nodes']['shear']]; seen=set();free=set()
        while todo:
            i=todo.pop()
            if i in seen:continue
            seen.add(i);n=b['nodes'][i]
            if n['kind']=='variable':free.add(n['name'])
            if 'left' in n:todo += [n['left'],n['right']]
        need('m' not in free,'triangular bijection '+variant)
        sig,th,U,V,m,rr=s.symbols('sig th U V m rr')
        cuts={b['named_nodes']['Sigma']:sig,b['named_nodes']['Theta']:th,
              b['named_nodes']['guard']:U,b['named_nodes']['lucas']:V,
              b['named_nodes']['shear']:rr}
        out=expression(b,cuts)(b['output'])
        formula=((sig*(m+rr)-th)**2-sig**2*(U+V))**2-4*sig**4*U*V
        need(s.expand(out-formula)==0,'literal final norm '+variant)
        inner=max(2*81925,81922+rd+81925,2*81922+294619,2*81922+dd)
        final=max(2*inner,4*81922+294619+458818)
        need(final==b['exact_degree'],'final degree bound '+variant)
        ans[variant]={'root_weighted_degree':rd,'defect_weighted_degree':dd,
                      'defect_terms':len(df.terms()),'final_degree_bound':final,
                      'literal_registers_verified':True,'shear_omits_m':True,
                      'final_norm_verified':True}
    result={'status':'PASS','method':'SymPy expansions independently reconstructed from literal named-register cuts; no import of builder or verify.py',
            'prefix_degrees':observed,'prefix_heads_nonzero_mod_1000003':True,'variants':ans,
            'note':'Exact attainment of the final bounds additionally follows from the explicit highest-degree products stated in root proof; fixed-prefix leading products were checked separately.'}
    OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
