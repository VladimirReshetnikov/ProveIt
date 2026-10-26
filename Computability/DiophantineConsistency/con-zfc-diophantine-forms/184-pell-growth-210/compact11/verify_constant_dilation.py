#!/usr/bin/env python3
"""Exact finite certificates for the constant-dilation compact polynomial.

The unbounded mathematics is in PROOF_constant_dilation.md. No zero search is
performed. Standard library only; conditions remain active under Python -O.
"""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from math import factorial
from pathlib import Path
import argparse, gzip, importlib.util, json

ROOT=Path(__file__).resolve().parent

def require(c,msg):
    if not c: raise ValueError(msg)

class Poly(dict):
    def __add__(self,b):
        b=P(b); out=Poly(self)
        for m,c in b.items():
            out[m]=out.get(m,0)+c
            if not out[m]:del out[m]
        return out
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.items()})
    def __sub__(self,b):return self+-P(b)
    def __rsub__(self,b):return P(b)+-self
    def __mul__(self,b):
        b=P(b);out=Poly()
        for m,c in self.items():
            for n,d in b.items():
                mn=tuple(sorted(m+n));out[mn]=out.get(mn,0)+c*d
        return Poly({m:c for m,c in out.items() if c})
    __rmul__=__mul__
    def __pow__(self,n):
        require(isinstance(n,int)and n>=0,'nonpolynomial exponent')
        a=P(1);b=self
        while n:
            if n&1:a=a*b
            b=b*b;n//=2
        return a

def P(v):
    if isinstance(v,Poly):return v
    if isinstance(v,str):return Poly({(v,):1})
    return Poly({():v})if v else Poly()

def op(o,a,b):
    if o=='+':return a+b
    if o=='-':return a-b
    if o=='*':return a*b
    raise ValueError('unknown op '+str(o))

def formulas():
    s={x:P(x)for x in ['beta','J','F','alpha','i','T','w','s','n','eta','zeta','kappa',
       'h','q','C','X','k','c','Am1','Delta','H','v0','ell','E','R','estar','B','U','a',
       'F0','f','Q','G','b','V','L','M','Z','P0','K','N','K0','MC','MF']}
    h,q,C,X,k,c,Am1,Delta,H,v0,ell,E,R,estar,B,U,a,F0,f,Q,G,b,V,L,M,Z,P0,K,N=[s[x]for x in
      ['h','q','C','X','k','c','Am1','Delta','H','v0','ell','E','R','estar','B','U','a',
       'F0','f','Q','G','b','V','L','M','Z','P0','K','N']]
    Y=s['s'];kap=s['kappa'];lam=210
    inverse=k-7350*v0*k*(k*k-4)+5402250*v0*v0*k*(k*k-4)*(27*k*k+8)
    inverse-=5672362500*v0**3*k*(k*k-4)*(675*k**4-324*k*k+160)
    return {
      'h':s['beta']*s['J'],'q':h+1,'C':q-s['F']-s['alpha'],
      'X':q*s['w'],'k':s['eta']+s['zeta'],'c':k*Y+s['eta'],
      'Am1':lam*Y*(X+1),'Delta':Am1*(Am1+2),'H':4*Am1-1,
      'v0':X*Y*Y,'ell':lam*lam*v0*k,'E':1+ell*(ell+k),
      'R':(h*(q-s['F'])+s['alpha'])*(q*q-1)+(s['MC']+q*s['MF'])*s['J'],
      'estar':inverse-R-1,'B':(s['K0']+s['w'])*C-s['F'],
      'U':s['i']*c*c,'a':Delta*U*U*E,'F0':a+1,'f':a+F0,
      'Q':4*Delta*a*F0,'G':E*F0,'b':c*s['T']-R,'V':f*b-c,'L':b*V,
      'M':h*q**7,
      'Z':M*(s['n']+kap-L*B)-q**7*B-h*(estar-q**4*Y),
      'P0':Q*(Z*Z-M*M*G*V*V)+(M*M*G-Z*Z),
      'K':X*(3*c-2*X)+2,'N':K-kap*H,'P':(P0+1)*(3*N+1)-1}

def check_graph(g):
    rows=g['source'];cuts=formulas();seen=set(g['witnesses']+g['fixed_numerals']);defs={}
    for name,o,a,b in rows:
        require(name not in seen,'duplicate '+name)
        require(o in ['+','-','*'],'invalid op')
        for arg in [a,b]:require(isinstance(arg,int)or arg in seen,'unbound '+str(arg))
        seen.add(name);defs[name]=(o,a,b)
    require(g['output']=='P','wrong output')
    live=set()
    def trace(x):
        if not isinstance(x,str)or x in live:return
        live.add(x)
        if x in defs:
            _,a,b=defs[x];trace(a);trace(b)
    trace('P')
    require(live==seen,'dead input or operation')
    visited=set()
    for target,expected in cuts.items():
        cache={}
        def eval_(x):
            if isinstance(x,int):return P(x)
            if x!=target and (x in cuts or x not in defs):return P(x)
            if x in cache:return cache[x]
            visited.add(x);o,a,b=defs[x]
            cache[x]=op(o,eval_(a),eval_(b));return cache[x]
        require(eval_(target)==expected,'formula differs at '+target)
    require(visited==set(defs),'unchecked gates: '+str(set(defs)-visited))
    require(len(rows)==104 and g['operations']==104,'operation count')
    require(len(g['witnesses'])==11,'variable count')
    require(dict(Counter(r[1]for r in rows))=={'*':61,'+':23,'-':20},'breakdown')
    return len(visited)

def truncate_x(p,N=4):return Poly({m:c for m,c in p.items()if m.count('x')<N})
def inverse_certificate():
    x,m=P('x'),P('m');lam=210
    def binpoly(shift,n):
        z=P(F(1,factorial(n)))
        for j in range(n):z=z*(m+shift-j)
        return z
    K=2*m+8*lam**2*binpoly(1,3)*x+32*lam**4*binpoly(2,5)*x*x+128*lam**6*binpoly(3,7)*x**3
    def mul(a,b):return truncate_x(a*b)
    def pow_(a,n):
        z=P(1)
        for j in range(n):z=mul(z,a)
        return z
    K2=mul(K,K);Fct=mul(K,K2-4)
    inverse=K-7350*mul(x,Fct)
    inverse+=5402250*mul(x*x,mul(Fct,27*K2+8))
    inverse-=5672362500*mul(x**3,mul(Fct,675*pow_(K,4)-324*K2+160))
    residue=truncate_x(inverse-2*m)
    require(not residue,'inverse identity failed')
    t=P('t');sign=675*t*t-1458*t-176
    require(sign==675*(t-4)**2+3942*(t-4)+4792,'sign decomposition')
    return {'coefficient_identities_in_Q_m':4,'lambda':lam,'residual_terms':0,
      'cleared_coefficients':[7350,5402250,5672362500],
      'positive_sign_decomposition':[675,3942,4792]}

def homogeneous(g):
    variables=set(g['witnesses']);forms={x:P(x)for x in g['witnesses']+g['fixed_numerals']};degrees={}
    def top(p):
        if not p:return -1,Poly()
        deg=max(sum(x in variables for x in mon)for mon in p)
        return deg,Poly({mon:c for mon,c in p.items()if sum(x in variables for x in mon)==deg})
    for name,o,a,b in g['source']:
        aa=P(a)if isinstance(a,int)else forms[a]
        bb=P(b)if isinstance(b,int)else forms[b]
        p=op(o,aa,bb);degree,t=top(p)
        # No ambiguous complete cancellation occurs at any addition/subtraction.
        require(p,'complete leading cancellation at '+name)
        forms[name]=t;degrees[name]=degree
    q0=P('beta')*P('J');k0=P('eta')+P('zeta');w,Y,i,kap=[P(x)for x in ['w','s','i','kappa']];lam=210
    expected0=-16*lam**36*q0**46*w**24*Y**56*i**10*k0**32*(q0-P('F'))**2
    require(forms['P0']==expected0,'P0 leading form')
    expected=-48*lam**36*q0**47*w**25*Y**56*i**10*k0**32*(q0-P('F'))**2*(3*k0*Y-2*q0*w-4*lam*kap*Y)
    require(forms['P']==expected,'full leading form')
    key=tuple(sorted(['beta']*49+['J']*49+['w']*25+['s']*57+['i']*10+['eta']*32+['kappa']))
    require(forms['P'].get(key)==192*lam**37,'fixed coefficient witness')
    require(degrees['P']==174,'exact total degree')
    require(tuple(degrees[x]for x in ['Q','M','G','V','Z'])==(58,8,36,30,44),'cut degrees')
    return {'exact_degree':174,'P0_degree':170,'leading_monomials':len(expected),
            'cut_degrees':{x:degrees[x]for x in ['Q','M','G','V','Z']},
            'coefficient_witness':'[J^49 w^25 s^57 i^10 eta^32 kappa] P = 192*210^37*beta^49 > 0'}

def coefficients(g):
    source=ROOT/'source140'/'rebuild_coefficients.py'
    spec=importlib.util.spec_from_file_location('frozen_coefficients',source)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    vals=module.reconstruct();receipt=[]
    for key,value in vals.items():
        meta=g['coefficient_binding']['ports'][key]
        raw=value.to_bytes((value.bit_length()+7)//8,'little')
        require(sha256(raw).hexdigest()==meta['raw_sha256'],'fixed coefficient differs '+key)
        require(value.bit_length()==meta['bits'],'fixed bitlength differs '+key)
        payload=(ROOT/g['coefficient_binding']['path']/meta['file']).read_bytes()
        require(sha256(payload).hexdigest()==meta['gzip_sha256'],'compressed payload differs '+key)
        actual=gzip.decompress(payload)
        require(actual==raw,'retained payload differs '+key)
        receipt.append({'port':key,'bits':value.bit_length(),'raw_sha256':sha256(raw).hexdigest()})
    require(vals['beta']>=31 and 0<vals['MC']<vals['beta']<vals['MF']<2*vals['beta'],'port box')
    return receipt

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt');ap.add_argument('--mutations',action='store_true');args=ap.parse_args()
    g=json.loads((ROOT/'constant_dilation11.json').read_text())
    r={'schema':'constant-dilation-review-v1','source_sha256':sha256((ROOT/'constant_dilation11.json').read_bytes()).hexdigest(),
       'operations':104,'variables':11,'checked_gates':check_graph(g),
       'inverse_certificate':inverse_certificate(),'degree_certificate':homogeneous(g),
       'coefficient_reconstruction':coefficients(g)}
    if args.mutations:
        count=0
        for row in g['source']:
            old=row[1]
            for new in ['+','-','*']:
                if new==old:continue
                row[1]=new
                try:check_graph(g)
                except ValueError:count+=1
                else:raise ValueError('undetected operation mutation '+str(row))
            row[1]=old
        r['rejected_operator_mutations']=count
    if args.receipt:Path(args.receipt).write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2))

if __name__=='__main__':main()
