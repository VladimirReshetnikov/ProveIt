#!/usr/bin/env python3
"""Exact numeral certificates for all three radix-three offset obstruction families.

The K/S rules are named derived-rule dependencies, justified by the supplied
parameter-generic M6.Logic.RestrictedImplication proof. This program does not
compile that proof and does not claim a new Lean or Rocq kernel certificate.
Membership vacuity and existential monotonicity are also named derived-rule
dependencies, with their fixed derivations given in theorem.tex. All three
residue families, including the offsets 0, 1 and 2, are checked.
"""
from math import isqrt
from pathlib import Path
import argparse,json

def pair(a,b):return (a+b)*(a+b+1)//2+b
def unpair(n):
    s=(isqrt(8*n+1)-1)//2;b=n-s*(s+1)//2;return s-b,b
def I(a,b):return 3*pair(a,b)
def U(d,a):return 3*pair(a,d)+2
def E(e,a,b):return 3*pair(a,b)+e
def M(a,b):return 3*pair(a,b)+1
def V(a,b,c):return I(M(a,b),U(c,M(a,b)))
def h3(e,c,a,b):return I(M(c,a),I(E(e,c,b),M(b,a)))
def h4(e,c,a,b):return I(E(e,c,a),I(M(b,c),M(b,a)))
def K(a,b):return I(a,I(b,a))
def S(a,b,c):return I(I(a,I(b,c)),I(I(a,b),I(a,c)))
def R(a,b,c,u):return I(I(I(c,u),a),I(I(a,c),I(b,c)))
def neg(a):return I(a,1)
def ex(d,a):return neg(U(d,neg(a)))
def h5(e,d,h):return ex(d,E(e,h,d))
def h1(d,h):return I(ex(d,U(d,h)),h)

class Proof:
    def __init__(self,e):self.e=e;self.lines=[]
    def add(self,rule,args,n):
        self.lines.append(dict(line=len(self.lines)+1,rule=rule,args=list(args),conclusion=n));return len(self.lines)
    def val(self,i):return self.lines[i-1]['conclusion']
    def mp(self,major,minor,n):return self.add('mp',(major,minor),n)
    def ident(self,a):
        p=self.add('K',(a,I(a,a)),K(a,I(a,a)))
        q=self.add('K',(a,a),K(a,a))
        r=self.add('S',(a,I(a,a),a),S(a,I(a,a),a))
        r=self.mp(r,p,I(K(a,a),I(a,a)))
        return self.mp(r,q,I(a,a))

def build(e):
    assert isinstance(e,int) and e>=0
    p=Proof(e)
    if e%3==0:
        k=e//3;x=k+1
        zero=p.add('rho8',(0,0,0,0),R(0,0,0,0));assert p.val(zero)==0
        kk=p.add('K',(0,x),K(0,x));t=I(x,0);tt=p.mp(kk,zero,t)
        residual=pair(t,1)-k;assert residual>=0
        h,d=unpair(residual);a=E(e,h,d);assert a==I(t,1)
        ident=p.ident(a)
        kk=p.add('K',(t,a),K(t,a));at=p.mp(kk,tt,I(a,t))
        ss=p.add('S',(a,t,1),S(a,t,1));ss=p.mp(ss,ident,I(I(a,t),I(a,1)));nn=p.mp(ss,at,neg(a))
        uu=p.add('gen',(d,nn),U(d,neg(a)));hh=p.add('head5',(d,h),h5(e,d,h));p.mp(hh,uu,1)
        witness={'offset':e,'k':k,'theorem_T':t,'h':h,'d':d,'E(h,d)':a,'I(T,1)':I(t,1),'collision':'E(h,d)=I(T,1) with T derived'}
    elif e%3==2:
        k=(e-2)//3;h,d=(1,0) if k==0 else (0,k-1)
        assert E(e,h,d)==U(d,1)
        h5line=p.add('head5',(d,h),h5(e,d,h));h1line=p.add('head1',(d,1),h1(d,1));p.mp(h1line,h5line,1)
        witness={'offset':e,'k':k,'h':h,'d':d,'E(h,d)':E(e,h,d),'U(d,1)':U(d,1),'collision':'E(h,d)=U(d,1)'}
    elif e==1:
        assert E(e,0,0)==1
        nn=p.ident(1);uu=p.add('gen',(0,nn),U(0,neg(1)));hh=p.add('head5',(0,0),h5(e,0,0));p.mp(hh,uu,1)
        witness={'offset':e,'h':0,'d':0,'E(h,d)':1,'collision':'E(0,0)=1'}
    else:
        k=(e-1)//3;assert k>=1
        m=M(k,k);m2=M(2*k,2*k)
        assert E(e,2*k,0)==m and E(e,3*k,k)==m2
        ww=p.add('head5',(0,2*k),h5(e,0,2*k))
        vv=p.add('membership_vacuity',(k,k,0),V(k,k,0))
        em=p.add('exists_mono',(0,vv,m,U(0,m)),I(ex(0,m),ex(0,U(0,m))))
        ee=p.mp(em,ww,ex(0,U(0,m)))
        hh=p.add('head1',(0,m),h1(0,m));mm=p.mp(hh,ee,m)
        ww=p.add('head5',(k,3*k),h5(e,k,3*k))
        vv=p.add('membership_vacuity',(2*k,2*k,k),V(2*k,2*k,k))
        em=p.add('exists_mono',(k,vv,m2,U(k,m2)),I(ex(k,m2),ex(k,U(k,m2))))
        ee=p.mp(em,ww,ex(k,U(k,m2)))
        hh=p.add('head1',(k,m2),h1(k,m2));mm2=p.mp(hh,ee,m2)
        ll=p.add('head3',(2*k,2*k,0),h3(e,2*k,2*k,0))
        ll=p.mp(ll,mm2,I(m,M(0,2*k)));ll=p.mp(ll,mm,M(0,2*k))
        rr=p.add('head4',(2*k,0,0),h4(e,2*k,0,0))
        rr=p.mp(rr,mm,I(M(0,2*k),1));p.mp(rr,ll,1)
        witness={'offset':e,'k':k,'E(2k,0)':E(e,2*k,0),'M(k,k)':m,'E(3k,k)':E(e,3*k,k),'M(2k,2k)':m2,'collision':'Two equality witnesses collapse to diagonal membership atoms'}
    return {'offset':e,'witness':witness,'lines':p.lines}

def check(obj):
    e=obj['offset'];values=[]
    for i,row in enumerate(obj['lines'],1):
        assert row['line']==i
        rule,args,n=row['rule'],row['args'],row['conclusion']
        assert isinstance(n,int) and n>=0
        assert all(isinstance(a,int) and a>=0 for a in args)
        def prev(j):
            assert isinstance(j,int) and 1<=j<i;return values[j-1]
        if rule=='rho8':assert args[3]<=args[0] and n==R(*args)
        elif rule=='K':assert n==K(*args)
        elif rule=='S':assert n==S(*args)
        elif rule=='head1':assert n==h1(*args)
        elif rule=='head5':assert n==h5(e,*args)
        elif rule=='head3':assert n==h3(e,*args)
        elif rule=='head4':assert n==h4(e,*args)
        elif rule=='membership_vacuity':
            a,b,c=args;assert c!=a and c!=b and n==V(a,b,c)
        elif rule=='exists_mono':
            d,line,a,b=args;assert prev(line)==I(a,b) and n==I(ex(d,a),ex(d,b))
        elif rule=='gen':assert n==U(args[0],prev(args[1]))
        elif rule=='mp':assert prev(args[0])==I(prev(args[1]),n)
        else:raise ValueError(rule)
        values.append(n)
    assert values[-1]==1
    return {'offset':e,'lines':len(values),'final_conclusion':values[-1],'rules':sorted({r['rule']for r in obj['lines']})}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'evidence');args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    examples=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,30,31,32,300,301,302]
    receipts=[]
    for e in examples:
        obj=build(e);receipts.append({**check(obj),'witness':obj['witness']});(args.output/f'offset_{e}.json').write_text(json.dumps(obj,indent=2)+'\n')
    # This is a bounded arithmetic check of the residue-one identities only.
    for k in range(1,10001):
        e=3*k+1
        assert E(e,2*k,0)==3*pair(k,k)+1
        assert E(e,3*k,k)==3*pair(2*k,2*k)+1
        assert 0!=k and k!=2*k
    result={'status':'PASS','certificates':receipts,'residue_one_bounded_identity_checks':10000,'derived_rule_dependencies':['M6.Logic.RestrictedImplication.k','M6.Logic.RestrictedImplication.s','membership vacuity from the guarded gate and old first head','existential monotonicity from contraposition, generalization and quantifier distribution'],'proof_boundary':'Exact numeric certificates in a conservative extension by the explicitly listed derived rules. The all-offset theorem is the separate mathematical argument; no new proof-assistant compilation.'}
    (args.output/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':
    if not __debug__:raise SystemExit('Assertions must remain enabled.')
    main()
