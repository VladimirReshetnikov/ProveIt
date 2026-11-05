#!/usr/bin/env python3
"""Exact modular and small full-integer controls for relaxed Pell integrality."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib,json
from pathlib import Path

def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def pairmul(a,b,D,mod=None):
    x,y=a;u,v=b;r=(x*u+D*y*v,x*v+y*u)
    return tuple(z%mod for z in r) if mod else r
def power(A,D,n,mod=None):
    need(n>=0,'negative index');out=(1,0);v=(A,1)
    while n:
        if n&1:out=pairmul(out,v,D,mod)
        v=pairmul(v,v,D,mod);n//=2
    return out

def analyze(A,p):
    D=A*A-1; xp,c=power(A,D,p);m=c
    need(A>=3 and p>0 and c>A*D*D,'large positive main ordinate')
    need(m%p==0 and m%c==0,'index divisibilities')
    # Only modular powering is used at the gigantic index; no giant Pell value is expanded.
    xmod,ymod=power(A,D,m,c*c)
    q,r=divmod(D*ymod,c*c)
    need(r==0 and q%D!=0 and ymod!=0,'relaxed divisibility or obstruction')
    return {'A':A,'Delta':D,'main_index':p,'main_root':xp,'c':c,'strong_index':m,
            'large_c_threshold':A*D*D,'y_mod_c_squared':ymod,'i_mod_Delta':q%D,
            'x_mod_c_squared':xmod,'modulus':c*c}
small=analyze(3,4)
x,y=power(3,8,204); c=204;i,rem=divmod(8*y,c*c)
need(rem==0 and i>0 and i%8==2 and y%(c*c)==10404,'small witness')
need(x*x-8*y*y==1 and (i*c*c)**2==8*(x*x-1),'full integer relaxed norm')
need(small['i_mod_Delta']==i%8,'small modular cross-check')
# Scale-realizable q-cube tuple, with c=(eta+zeta)*Y+eta.
big=analyze(191,6);q=3;s=1;w=2;X=w*q;Y=s*q**3;a=(X+1)*Y
need(a+2==191,'q-cube parameter');k,eta=divmod(big['c'],Y);zeta=k-eta
need(0<eta and 0<zeta and k==eta+zeta and big['c']==k*Y+eta,'positive eta/zeta representation')
need(big['c']==8134013891706 and big['strong_index']==big['c'],'big explicit coordinate')
need(big['i_mod_Delta']==6080,'symbolic obstruction residue')
print(json.dumps({'status':'PASS','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'small_full_integer':{**small,'f_bits':x.bit_length(),'y_bits':y.bit_length(),'i_bits':i.bit_length()},
 'symbolic_qcube':{**big,'q':q,'s':s,'w':w,'X':X,'Y':Y,'k':k,'eta':eta,'zeta':zeta},
 'scope':'Standard-integer relaxed Pell/coordinate data only; no full graph zero, fixed-current-port instance, IΣ₁ theorem or existential inequivalence.'},indent=2,sort_keys=True))
