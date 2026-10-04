"""Fresh independent static transcription/algebra checks; no imported scientific code.
All inputs are read inertly. No physical or source-machine execution is performed.
"""
from pathlib import Path
from fractions import Fraction as F
from math import gcd
import hashlib, json, re, sys
root=Path(__file__).resolve().parent.parent
texpath=Path(sys.argv[1]) if len(sys.argv)>1 else root/'inputs'/'Report65.tex'
tex=texpath.read_text()
checks={}

def norm(s):
    s=re.sub(r'\\label\{[^}]*\}|\\nonumber','',s)
    return re.sub(r'\s+','',s)
expected=[r'x_i^2-1-(\alpha_i^2-1)y_i^2',r'u_i^2-1-(\alpha_i^2-1)v_i^2',
 r's_i^2-1-(\beta_i^2-1)t_i^2',r'\beta_i-1-4y_iq_{b,i}',
 r'\beta_i+u_i\alpha_{1,i}-\alpha_i-u_i\alpha_{2,i}',r'v_i-y_i^2q_{v,i}',
 r's_i+u_i\sigma_{1,i}-x_i-u_i\sigma_{2,i}',r't_i+4y_i\tau_{1,i}-C-4y_i\tau_{2,i}',
 r'y_i-C-d_{yC,i}',r'w_i-2-d_{w2,i}',r'w_i-C-d_{wC,i}',r'M_i-2o-J_i',
 r'\alpha_i^2-1-\bigl((w_i+1)^2-1\bigr)(w_i\eta_i)^2',r'4\alpha_i-M_i-5',
 r'x_i+M_ir_{1,i}-y_i(\alpha_i-2)-2o-M_ir_{2,i}']
for side,out in [('A','P'),('B','Q')]:
    anchor=tex.index('\\subsection{The '+side+' module}')
    begin=tex.index('\\begin{align}',anchor)+len('\\begin{align}')
    end=tex.index('\\end{align}',begin)
    rows=tex[begin:end].split('\\\\')
    rows=[norm(r).replace('&=0,','').replace('&=0.','') for r in rows]
    want=[norm(s.replace('_i','_'+side).replace(',i}',','+side+'}').replace('C',side).replace('2o','2'+out)) for s in expected]
    # The three slack names retain C as a semantic index symbol: restore those names.
    want=[s.replace('d_{y'+side+',','d_{yC,').replace('d_{w'+side+',','d_{wC,') for s in want]
    assert rows==want,[(i,a,b) for i,(a,b) in enumerate(zip(rows,want),1) if a!=b]
    checks['module_'+side+'_exact_display_match']=len(rows)

# Small, inspected sparse integer-polynomial implementation owned by this review.
# A monomial is a sorted tuple of variable names, with repetition for exponents.
class P:
    def __init__(self,value=0):
        self.d=value if isinstance(value,dict) else ({():value} if value else {})
        self.d={m:c for m,c in self.d.items() if c}
    @staticmethod
    def v(name): return P({(name,):1})
    def __add__(self,other):
        other=other if isinstance(other,P) else P(other); d=self.d.copy()
        for m,c in other.d.items(): d[m]=d.get(m,0)+c
        return P(d)
    __radd__=__add__
    def __neg__(self): return P({m:-c for m,c in self.d.items()})
    def __sub__(self,other): return self+-P.coerce(other)
    def __rsub__(self,other): return P.coerce(other)+-self
    @staticmethod
    def coerce(a): return a if isinstance(a,P) else P(a)
    def __mul__(self,other):
        other=P.coerce(other); d={}
        for m,c in self.d.items():
            for n,e in other.d.items():
                k=tuple(sorted(m+n)); d[k]=d.get(k,0)+c*e
        return P(d)
    __rmul__=__mul__
    def __pow__(self,n):
        ans=P(1)
        for _ in range(n): ans=ans*self
        return ans
    def degree(self): return max(map(len,self.d),default=-1)
    def evaluate(self,values):
        ans=0
        for m,c in self.d.items():
            for name in m: c*=values[name]
            ans+=c
        return ans

leaves='o w M eta x y u v s t qb qv J ap bp dw2 dwC dyC a1 a2 s1 s2 t1 t2 r1 r2'.split()
assert len(leaves)==len(set(leaves))==26

def module(side,shift=False):
    z={k:P.v(side+'_'+k) for k in leaves}
    o,w,M,eta,x,y,u,v,s,t,qb,qv,J=[z[k] for k in leaves[:13]]
    alpha=z['ap']+1; beta=z['bp']+1
    dw2,dwC,dyC,a1,a2,s1,s2,t1,t2,r1,r2=[z[k]-1 for k in leaves[15:]]
    C=P.v(side+'_C')
    if shift: a1=a1+P.v('n'); a2=a2+P.v('n')
    return [x*x-1-(alpha*alpha-1)*y*y,u*u-1-(alpha*alpha-1)*v*v,
      s*s-1-(beta*beta-1)*t*t,beta-1-4*y*qb,beta+u*a1-alpha-u*a2,
      v-y*y*qv,s+u*s1-x-u*s2,t+4*y*t1-C-4*y*t2,y-C-dyC,
      w-2-dw2,w-C-dwC,M-2*o-J,alpha*alpha-1-((w+1)**2-1)*(w*eta)**2,
      4*alpha-M-5,x+M*r1-y*(alpha-2)-2*o-M*r2]
mods={s:module(s) for s in 'AB'}
for side,rs in mods.items():
    degrees=[r.degree() for r in rs]
    assert degrees==[4,4,4,2,2,3,2,2,1,1,1,1,6,1,2]
    assert all(a.d==b.d for a,b in zip(rs,module(side,True)))
    fixture={k:1 for k in leaves}; fixture.update(o=1,w=2,M=63,eta=3,x=17,y=1,u=577,v=34,s=17,t=1,qb=4,qv=34,J=61,ap=16,bp=16,dwC=2,C=1)
    values={side+'_'+k:v for k,v in fixture.items()}
    assert all(r.evaluate(values)==0 for r in rs)
    checks[side+'_degrees']=degrees
    checks[side+'_exponent_zero_residuals']=[r.evaluate(values) for r in rs]
    checks[side+'_common_shift_invariance']=True
squares=sum((r*r for rs in mods.values() for r in rs),P())
leading={','.join(m):c for m,c in squares.d.items() if len(m)==12}
assert leading=={','.join(sorted([s+'_w']*8+[s+'_eta']*4)):1 for s in 'AB'}
checks['POWER_square_degree']=squares.degree(); checks['degree12_monomials']=leading

inc=F(3)+2*(F(1,2)+F(1,2)/(1-F(1,40)))
dec=F(6)+2*(2+F(2)/(1+F(1,20)))
pos=F(250,9)+dec
assert (inc,dec,pos)==(F(196,39),F(290,21),F(2620,63))
rows=[(2-inc/20,2*inc,F(0),14),(F(0),F(50,9),F(25,9),14),
 (2+pos/40,pos/2,F(0),26),(4+inc*F(39,20),F(0),-2*inc,20),
 (F(31,3),F(-25,9),F(-50,9),20),(4+pos*F(21,40),F(0),-pos/2,32)]
ks=[]; totals=[]; padding=[]
for alpha,beta,gamma,events in rows:
    lX,rX=max(-beta,0),max(beta,0); lY,rY=max(-gamma,0),max(gamma,0)
    k=30-alpha-rX-rY-4
    assert k>0 and alpha+(4+k)+rX+rY==30 and beta+lX-rX==0 and gamma+lY-rY==0
    target=2*bool(lX)+4*bool(lY)+4*bool(rX)+2*bool(rY)
    ks.append(k); padding.append(18+target); totals.append(events+18+target)
assert ks==[F(71,5),F(53,3),F(13,6),F(61,5),F(47,3),F(1,6)]
assert totals==[36,38,48,42,44,54]
core={F(1),F(1,3),F(1,79),F(1,41),F(3,2),F(1,4),F(4),F(1,2),F(2)}
added={F(39,196),F(18,25),F(9,25),F(63,655)}|{2/k for k in ks}
assert len(core)==9 and len(added)==10 and not core&added
checks['clock_rows']=[[str(x) for x in r] for r in rows]
checks['clock_k']=[str(x) for x in ks]; checks['padding_contacts']=padding
checks['instruction_contacts']=totals; checks['common_speeds']=1+2*len(core|added)

# Literal trace ledger reconstructed from the stated index sets, retaining zero slots.
tracecases=[]
for E,Z in [(1,0),(2,0),(3,1),(8,3)]:
    for T in [0,1,2,7]:
        slots=1 if T==0 else T*E+T+2*T+T*Z+1+(T-1)+1
        witnesses=T*E+2*T
        assert slots==T*(E+Z+4)+1 and witnesses==T*(E+2)
        tracecases.append({'E':E,'Z':Z,'T':T,'full_witnesses':witnesses+2+2*len(leaves),'full_slots':slots+2+30})
checks['trace_ledger_cases']=tracecases

# Finite support for the independently read gcd/Bezout all-pair argument.
for a in range(65):
    for b in range(65):
        m=max(a,b); U=2**m+2**(m-a+1); W=2**m+2**(m-b+1); V=20*2**m-U-W
        c=gcd(gcd(U,V),W)
        predicted=1 if m==0 else 4 if a==b==1 else 2 if m==1 else 10 if a%4==b%4==3 else 2
        assert c==predicted
        g=(U//c,V//c,W//c); D=sum(g)
        expectedbit=5 if m==0 else 4 if a==b==1 else 5 if m==1 else m+2 if c==10 else m+4
        assert D.bit_length()==expectedbit
        assert D.bit_length()-1<=max(x.bit_length() for x in g)<=D.bit_length()
        assert (20*g[0]-D)*2**a==2*D and (20*g[2]-D)*2**b==2*D
checks['normalization_finite_grid']={'a':[0,64],'b':[0,64],'pairs':65**2,'all_passed':True}
checks['manuscript_sha256']=hashlib.sha256(texpath.read_bytes()).hexdigest()
checks['utility_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
checks['limits']='Static support only; no physical simulation, interpreter, source execution, Lean run, or replacement of all-input proof arguments.'
output=root/'review'/('static-'+checks['manuscript_sha256'][:12]+'.json')
output.write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps({'passed':True,'output':str(output),'sha256':hashlib.sha256(output.read_bytes()).hexdigest()},indent=2))
