"""Independent finite residue/tail audit for the all-degree Gamma-Appell bridge."""
from pathlib import Path
import json,sympy as S,time
V=Path(__file__).resolve().parent;mmax=7
h=S.symbols('h1:10');z={j:S.Symbol('z'+str(j)) for j in range(2,11)};a={j:S.Symbol('A'+str(j)) for j in range(2,11)};v=S.Symbol('v');y=S.Symbol('y');t=S.Symbol('t');g=S.Symbol('gamma')
# Coefficients of exp(h1*t + sum(z_j*t^j/j)), via t differentiation.
Phi=[S.Integer(1)]
for m in range(1,mmax+1):Phi.append(S.expand(sum((h[0] if j==1 else z[j])*Phi[m-j]/S.factorial(m-j) for j in range(1,m+1))*S.factorial(m-1)))
e=[S.Integer(1)]
for r in range(1,mmax):e.append(S.expand(sum((-1)**(j-1)*h[j-1]*e[r-j] for j in range(1,r+1))/r))
# Laurent coefficients using exact sparse convolution, no source compiler.
def mul(p,q,cap):
 out={}
 for i,c in p.items():
  for j,d in q.items():
   if i+j<=cap:out[i+j]=S.expand(out.get(i+j,0)+c*d)
 return out
even_rules={z[2*r]:(-1)**(r+1)*S.bernoulli(2*r)*2**(2*r-1)*6**r*z[2]**r/S.factorial(2*r) for r in range(2,6)}

from collections import Counter
from functools import lru_cache
from itertools import combinations
import ast,hashlib
B=V.parent;C=B.parent/'reports/stieltjes-harmonic-resonance/continuations/differential-polygamma-lerch-jets/verification/digamma_continuation'
def reduce(p):return S.expand(S.expand(p).xreplace(even_rules))
@lru_cache(None)
def quasi(a,b):
 out=Counter();stack=[((),a,b)]
 while stack:
  prefix,x,y=stack.pop()
  if not x or not y:out[prefix+x+y]+=1;continue
  stack.extend([(prefix+(x[0],),x[1:],y),(prefix+(y[0],),x,y[1:]),(prefix+(x[0]+y[0],),x[1:],y[1:])])
 return dict(out)
def productword(indices):
 out={():1}
 for x in indices:
  nxt=Counter()
  for w,c in out.items():
   for t,d in quasi(w,(x,)).items():nxt[t]+=c*d
  out=dict(nxt)
 return out
def compositions(n):
 if n==0:return [()]
 return [(j,)+p for j in range(1,n+1) for p in compositions(n-j)]
def admissible(n):return [p for p in compositions(n) if p[0]>=2]
def binary(w):return tuple(x for n in w for x in (0,)*(n-1)+(1,))
def indices(w):
 p=[];k=1
 for x in w:
  if x:k1=k;p.append(k1);k=1
  else:k+=1
 assert k==1;return tuple(p)
def integral_shuffle(a,b):
 x,y=binary(a),binary(b);out=Counter()
 for pos in combinations(range(len(x)+len(y)),len(x)):
  chosen=set(pos);i=j=0;w=[]
  for k in range(len(x)+len(y)):
   if k in chosen:w.append(x[i]);i+=1
   else:w.append(y[j]);j+=1
  out[indices(w)]+=1
 return dict(out)
def dual(w):return indices(tuple(1-x for x in binary(w)[::-1]))
known={(2,):z[2],(3,):z[3],(4,):z[4],(2,1):z[3],(3,1):z[4]/4,(2,2):3*z[4]/4,(2,1,1):z[4]}
certificates=[]
for weight in (5,6):
 words=admissible(weight);index={w:i for i,w in enumerate(words)};rows=[];rhs=[];labels=[]
 def add(label,row,value=0):
  r=[S.Integer(0)]*len(words)
  for w,c in row.items():
   if c:assert w in index,(label,w);r[index[w]]+=c
  rows.append(r);rhs.append(reduce(value));labels.append(label)
 add('single',{(weight,):1},z[weight])
 for w in words:
  row=Counter();row[w]+=1;row[dual(w)]-=1;add('duality '+str(w),row)
 for k in range(2,weight-1):
  for left in admissible(k):
   for right in admissible(weight-k):
    value=known[left]*known[right];add('stuffle '+str((left,right)),quasi(left,right),value);add('shuffle '+str((left,right)),integral_shuffle(left,right),value)
 for w in admissible(weight-1):
  row=Counter(quasi((1,),w))
  for t,c in integral_shuffle((1,),w).items():row[t]-=c
  add('one-divergence '+str(w),{t:c for t,c in row.items() if c})
 M=S.Matrix(rows);R=S.Matrix(rhs);selected=list(M.T.rref()[1]);assert len(selected)==len(words);square=M[selected,:];inv=square.inv();assert inv*square==square*inv==S.eye(len(words));solution=inv*R[selected,:];assert all(reduce(x)==0 for x in M*solution-R)
 if weight==6:
  supplied=json.loads((C/'mzv6_relations.json').read_text());assert words==[tuple(w) for w in supplied['words']];assert M==S.Matrix([[S.Rational(c) for c in r] for r in supplied['matrix']]);assert all(reduce(x-S.sympify(c,locals={str(q):q for q in z.values()}))==0 for x,c in zip(R,supplied['rhs']))
 corrupt=solution.copy();corrupt[0]+=z[weight];assert any(reduce(x)!=0 for x in M*corrupt-R)
 known.update({w:solution[i] for i,w in enumerate(words)})
 certificates.append(dict(weight=weight,words=[list(w) for w in words],rows=len(rows),rank=len(words),matrix=[[str(c) for c in r] for r in rows],rhs=[str(c) for c in rhs],row_labels=labels,selected_rows=selected,selected_inverse=[[str(c) for c in r] for r in inv.tolist()],solutions={str(w):str(solution[i]) for i,w in enumerate(words)},both_inverse_products=True,all_row_residuals_zero=True,corruption_rejected=True))
 print('Independent weight',weight,len(rows),'rows rank',len(words),flush=True)
records=[]
def marked(w,j):return S.Symbol('d_'+'_'.join(map(str,w))+'__'+str(j))
def direction(w,i,j):return marked(w,i)-marked(w,j)
def dz(k):return marked((k,),1)
printed6=120*z[2]*direction((2,1),1,2)-60*direction((2,2,1),2,3)+120*direction((3,1,1),1,2)-180*direction((4,1),1,2)-30*direction((2,3),1,2)+138*dz(5)-60*z[2]*dz(3)+30*z[3]*dz(2)
printed7=840*z[2]*direction((2,1,1),1,2)-840*z[2]*direction((3,1),1,2)+210*z[2]*marked((2,2),1)-420*direction((2,2,1,1),2,3)+630*direction((2,3,1),2,3)+840*direction((3,1,1,1),1,2)+420*direction((3,1,2),1,2)+210*(2*direction((3,2,1),1,3)+direction((3,2,1),2,3))+210*marked((2,2,2),1)+798*marked((3,3),1)-1260*direction((4,1,1),1,2)+168*direction((2,4),1,2)+1596*direction((5,1),1,2)+S.Rational(651,2)*z[4]*dz(2)+336*z[2]*dz(4)-378*z[3]*dz(3)-504*dz(6)
sub={marked((2,2),2):z[2]*dz(2)-dz(4)-marked((2,2),1),marked((3,3),2):z[3]*dz(3)-dz(6)-marked((3,3),1),marked((3,2),1):z[2]*dz(3)-dz(5)-marked((2,3),2),marked((3,2),2):z[3]*dz(2)-dz(5)-marked((2,3),1),marked((4,2),1):z[2]*dz(4)-dz(6)-marked((2,4),2),marked((4,2),2):z[4]*dz(2)-dz(6)-marked((2,4),1),marked((2,2,2),3):S.Rational(3,4)*z[4]*dz(2)-z[2]*dz(4)+dz(6)-marked((2,2,2),1)-marked((2,2,2),2)}
for m in (6,7):
 psi={-1:S.Integer(-1),0:h[0]}|{r-1:h[r-1]+(-1)**r*z[r] for r in range(2,m+1)};powers=[{0:S.Integer(1)}]
 for k in range(1,m+1):powers.append(mul(powers[-1],psi,m-k-1))
 scalar=S.Poly(Phi[m],h[0]);principal={j:S.expand(sum(c*powers[k[0]].get(-j,0) for k,c in scalar.terms())) for j in range(1,m+1)}
 Jpoly=reduce(sum((q.subs({h[r-1]:h[r-1]+v**r for r in range(1,m+1)},simultaneous=True)-q)*v**(j-1)/S.Integer(j-1) for j,q in principal.items() if j>=2));Jwords={}
 for ex,c in S.Poly(Jpoly,v,*h[:m]).terms():
  if not c:continue
  assert ex[0]>=2
  for w,d in productword(tuple(r for r,n in enumerate(ex[1:],1) for _ in range(n))).items():key=(ex[0],)+w;Jwords[key]=reduce(Jwords.get(key,0)+c*d)
 J=reduce(sum(c*known[w] for w,c in Jwords.items()));expected=245*z[2]*z[3]+175*z[5] if m==6 else S.Rational(3731,4)*z[3]**2+S.Rational(918631,240)*z[6];assert reduce(J-expected)==0,(m,J)
 defect=reduce(principal[1]+S.factorial(m)*e[m-1]);tail=reduce(defect.subs({h[r-1]:z[r]-a[r] for r in range(2,m+1)},simultaneous=True));difference=reduce(tail.subs(h[0],h[0]+v)-tail.subs({a[r]:a[r]+v**r for r in range(2,m+1)},simultaneous=True));Dwords={}
 for ex,c in S.Poly(difference,v,h[0],*[a[r] for r in range(2,m+1)]).terms():
  if not c:continue
  q,b,*upper=ex;assert q>=1
  upinds=tuple(r for r,n in enumerate(upper,2) for _ in range(n));assert upinds or q>=2
  for up,um in productword(upinds).items():
   for low,lm in productword((1,)*b).items():key=(up+(q,)+low,len(up)+1);Dwords[key]=reduce(Dwords.get(key,0)+c*um*lm)
 raw=S.expand(sum(c*marked(w,j) for (w,j),c in Dwords.items()));printed=printed6 if m==6 else printed7;assert reduce(raw.subs(sub,simultaneous=True)-printed)==0
 assert reduce(raw.subs(sub,simultaneous=True)-(printed+dz(m-1)))!=0
 records.append(dict(degree=m,principal_coefficients={str(j):str(q) for j,q in principal.items()},Jpolynomial=str(Jpoly),Jwords={str(w):str(c) for w,c in Jwords.items() if c},J_reduced=str(expected),tail_defect=str(tail),difference=str(difference),Dwords={str(k):str(c) for k,c in Dwords.items() if c},printed_directional_formula_verified=True,derivative_corruption_rejected=True))
 print('Degree',m,'J and every marked coefficient PASS',flush=True)
out=dict(status='PASS',ordinary_certificates=certificates,moments=records,supplied_weight_six_rows_regenerated=49,source_certificate_sha256=hashlib.sha256((C/'mzv6_relations.json').read_bytes()).hexdigest(),scope='Independent binary-shuffle placement enumeration, stack stuffle, sparse pole convolution and rational matrix certificates. Derivative simplifications use only open-domain stuffle identities. Finite certificates instantiate the proved all-degree analytic bridge; no arithmetic independence or numerical interval claim.')
(V/'appell-six-seven-exact.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
