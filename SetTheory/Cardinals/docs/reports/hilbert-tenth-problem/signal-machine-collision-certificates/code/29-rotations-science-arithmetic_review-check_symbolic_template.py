"""Fresh sparse-polynomial checker for one arithmetic template, not a frontend.
No inherited source is loaded. U,V,Q stand for linear input forms. The toy
quadratic radius residual models degree only; it makes no geometric claim.
"""
import json
from pathlib import Path

class P:
    def __init__(self,x=0):
        self.d=x if isinstance(x,dict) else ({():x} if x else {})
    @staticmethod
    def of(x): return x if isinstance(x,P) else P(x)
    def __add__(self,x):
        d=dict(self.d)
        for k,v in P.of(x).d.items():
            d[k]=d.get(k,0)+v
            if not d[k]: del d[k]
        return P(d)
    __radd__=__add__
    def __neg__(self): return P({k:-v for k,v in self.d.items()})
    def __sub__(self,x): return self+-P.of(x)
    def __rsub__(self,x): return P.of(x)+-self
    def __mul__(self,x):
        d={}
        for k,v in self.d.items():
            for l,w in P.of(x).d.items():
                z=tuple(sorted(k+l))
                d[z]=d.get(z,0)+v*w
        return P({k:v for k,v in d.items() if v})
    __rmul__=__mul__
    def __pow__(self,n):
        assert n>=0
        r=P(1)
        for _ in range(n): r=r*self
        return r
    @property
    def degree(self): return max(map(len,self.d),default=-1)

leaves=[]
def var(name,witness=True):
    if witness:
        assert name not in leaves
        leaves.append(name)
    return P({(name,):1})
def pos(name): return var(name)
def nat(name): return var(name+'.plus')-1
def sig(name): return var(name+'.positive')-var(name+'.negative')

def power(prefix,base,e):
    before=len(leaves)
    vals={x:pos(prefix+'.'+x) for x in ('out','w','M','g','x','y','u','v','s','t','qb','qv','Jp')}
    vals.update({x:pos(prefix+'.'+x)+1 for x in ('a','beta')})
    vals.update({x:nat(prefix+'.'+x) for x in ('dwb','dwk','dyk','alpha1','alpha2','sigma1','sigma2','tau1','tau2','rho1','rho2')})
    out,w,M,g,x,y,u,v,s,t,qb,qv,Jp=(vals[z] for z in ('out','w','M','g','x','y','u','v','s','t','qb','qv','Jp'))
    a,beta=(vals[z] for z in ('a','beta'))
    dwb,dwk,dyk,al1,al2,sg1,sg2,ta1,ta2,rh1,rh2=(vals[z] for z in ('dwb','dwk','dyk','alpha1','alpha2','sigma1','sigma2','tau1','tau2','rho1','rho2'))
    k=e+1; m=base*out
    residuals=[
        x*x-1-(a*a-1)*y*y,
        u*u-1-(a*a-1)*v*v,
        s*s-1-(beta*beta-1)*t*t,
        beta-1-4*y*qb,
        beta+u*al1-a-u*al2,
        v-y*y*qv,
        s+u*sg1-x-u*sg2,
        t+4*y*ta1-k-4*y*ta2,
        y-k-dyk,
        w-base-dwb,
        w-k-dwk,
        M-m-Jp,
        a*a-1-((w+1)*(w+1)-1)*(w*g)*(w*g),
        2*a*base-M-base*base-1,
        x+M*rh1-y*(a-base)-m-M*rh2]
    assert len(leaves)-before==26 and len(residuals)==15
    assert residuals[12].degree==6
    return out,residuals

# A fixed primitive triple with negative real and imaginary components.
a,b,c=-16,-63,65
U,V,Q=(var(x,False) for x in ('U','V','Q'))
delta=nat('delta')
n,k,LC,HC,LS,HS=(nat(x) for x in ('n','k','LC','HC','LS','HS'))
h,q,r,s,t,J=(pos(x) for x in ('h','q','r','s','t','J'))
u,v,a1,a2,a3,C,S,kappa=(sig(x) for x in ('u','v','a1','a2','a3','C','S','kappa'))
Pout,mod1=power('power_c',P(c),n)
B=4*Pout+2*c+1
Tout,mod2=power('power_extract',a+abs(b)*B,n)
residuals=[Q*Q-U*U-V*V-delta,
    U-h*u,V-h*v,Q-h*q,a1*u+a2*v+a3*q-1,
    q-Pout*r,r-c*k-s,s+t-c,
    C+Pout-LC,Pout-C-HC,S+Pout-LS,Pout-S-HS,
    Tout-C-B*S-kappa*(B*B+1),
    delta*delta+(r-1)*(r-1)+(u-C)*(u-C)+(v-S)*(v-S)-J]
assert len(residuals)==14
outer_degrees=[x.degree for x in residuals]
residuals+=mod1+mod2
F=sum((x*x for x in residuals),P(0))
assert len(leaves)==81 and len(residuals)==44 and F.degree==12
for pref in ('power_c','power_extract'):
    monomial=tuple(sorted([pref+'.w']*8+[pref+'.g']*4))
    assert F.d[monomial]==1
result={'template_constants':{'a':a,'b':b,'c':c},'positive_witnesses':len(leaves),
'equations':len(residuals),'outer_residual_degrees':outer_degrees,
'module_residual_degrees':[[x.degree for x in mod1],[x.degree for x in mod2]],
'exact_sum_of_squares_degree':F.degree,'sum_of_squares_monomials':len(F.d),
'caveat':'One arithmetic template only; U,V,Q are formal linear input forms and the radius residual is a degree model, not a physical frontend.',
'result':'all assertions passed'}
Path(__file__).with_name('symbolic_template_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
