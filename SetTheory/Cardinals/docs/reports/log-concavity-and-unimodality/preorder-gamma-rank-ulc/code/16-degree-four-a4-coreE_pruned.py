"""Exact certificates for the degree5 core correction E on nonnegative integer populations.

Cone: averages of B_m(n) f(n-m)^2, plus a nonnegative B_e remainder.
Every emitted certificate uses the established ordinary-binomial square schema.
The numerical LP only discovers weights; all claims undergo Fraction verification.
"""
from integer_sos_common import *
CORE={r['id']:r for r in map(json.loads,(D/'core_corrections.jsonl').read_text().splitlines())}
from scipy.sparse import hstack,eye
import subprocess, argparse

if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)

def exact_gmp_solve(M,rhs):
 rows=[]
 for i in range(M.rows):
  row=[F(M[i,j]) for j in range(M.cols)]+[F(rhs[i,0])]
  den=math.lcm(*(v.denominator for v in row));ints=[v.numerator*(den//v.denominator) for v in row]
  g=math.gcd(*ints);rows.append(' '.join(str(v//g if g else v) for v in ints))
 answer=subprocess.run([str(D/'exact_bareiss_remaining')],input=f'{M.rows} {M.cols}\n'+'\n'.join(rows)+'\n',text=True,capture_output=True,check=True).stdout
 ww=[F(v) for v in answer.split()];assert len(ww)==M.cols
 assert all(sum((F(M[i,j])*ww[j] for j in range(M.cols)),F(0))==F(rhs[i,0]) for i in range(M.rows))
 return ww

def main(tid,iterations=150,initial_target_only=False,lp_method="highs",prune_columns=False):
 start=time.time();d=T[tid]['variables'];actions=[a['variable_map'] for a in O[tid]['actions']];target=dict(CORE[tid]['E'])
 def support(code):return sum(1<<i for i in range(d) if (code>>(3*i))&7)
 def factorial_product(code):return math.prod(math.factorial((code>>(3*i))&7) for i in range(d))
 def leading_value(code,S,top):return F(1,factorial_product(code)) if degree(code)==top and support(code)&~S==0 else F(0)
 @lru_cache(maxsize=None)
 def images(code):
  digits=[(i,(code>>(3*i))&7) for i in range(d) if(code>>(3*i))&7]
  return tuple(sum(q<<(3*perm[i]) for i,q in digits) for perm in actions)
 def aggregate(p):
  out={}
  for e,c in p.items():
   q=min(images(e));out[q]=out.get(q,0)+c
  return {e:c for e,c in out.items() if c}
 @lru_cache(maxsize=200000)
 def bchoose(n,q):
  z=1
  while n or q:
   a=n&7;b=q&7
   if b>a:return 0
   z*=math.comb(a,b);n>>=3;q>>=3
  return z
 @lru_cache(maxsize=None)
 def evaluate(n):return sum(target.get(e,0)*bchoose(n,e) for e in lower_box(n))
 @lru_cache(maxsize=None)
 def lower_box(q):
  out=[0]
  for i in range(d):out=[e+(r<<(3*i)) for e in out for r in range(((q>>(3*i))&7)+1)]
  return tuple(out)
 @lru_cache(maxsize=300000)
 def product3(a,b,m):
  return tuple((m+e,c*bchoose(m+e,m)) for e,c in bp(a,b))
 def full_square_shifted(z,m):
  # Clear denominators once; all inner products then use fast integer arithmetic.
  den=math.lcm(*(F(u).denominator for u in z.values())) if z else 1
  items=[(a,F(u).numerator*(den//F(u).denominator)) for a,u in z.items()]
  out={}
  for i,(a,u) in enumerate(items):
   for j in range(i,len(items)):
    b,v=items[j];factor=u*v*(1 if i==j else 2)
    for e,c in product3(a,b,m):out[e]=out.get(e,0)+factor*c
  return {e:F(c,den*den) for e,c in out.items() if c}
 def shifted_to_ordinary(z,m):
  # binom(n_i-m_i,q_i)=sum_r binom(-m_i,q_i-r_i)binom(n_i,r_i).
  out={}
  for q,c in z.items():
   terms=[(0,F(c))]
   for i in range(d):
    qi=(q>>(3*i))&7;mi=(m>>(3*i))&7;next_terms=[]
    for r in range(qi+1):
     k=qi-r;coeff=((-1)**k*math.comb(mi+k-1,k)) if mi else int(k==0)
     if coeff:next_terms.extend((e+(r<<(3*i)),a*coeff) for e,a in terms)
    terms=next_terms
   for e,a in terms:out[e]=out.get(e,F(0))+a
  return {e:a for e,a in out.items() if a}
 def full_square_ordinary(z,m):
  out={}
  for a,u in z.items():
   for b,v in z.items():
    for e,c in bp(a,b):
     for f,k in bp(e,m):out[f]=out.get(f,F(0))+u*v*c*k
  return {e:c for e,c in out.items() if c}
 leading={S:sum(F(c,factorial_product(e)) for e,c in target.items() if degree(e)==5 and support(e)&~S==0) for S in range(1,1<<d)}
 zeros=[S for S,v in leading.items() if not v];assert all(v>=0 for v in leading.values())
 (D/f'coreE_leading_zeros_{tid}.json').write_text(json.dumps({'template':tid,'degree':5,'binary_zero_directions':zeros,'negative_binary_directions':[]})+'\n')
 aggregated=aggregate(target);E=sorted({min(images(e)) for e in exps(d,5)});ix={e:i for i,e in enumerate(E)};seen=set();cols=[];metadata=[]
 val=np.array([aggregated.get(e,0) for e in E],dtype=float)
 def sparse_columns(polys):
  rr=[];cc=[];vv=[]
  for j,p in enumerate(polys):
   for e,c in p.items():rr.append(ix[e]);cc.append(j);vv.append(float(c))
  return csc_matrix((vv,(rr,cc)),shape=(len(E),len(polys)))
 def append_ray(m,z,outcols,outmeta,dual=None):
  z={a:c for a,c in z.items() if c}
  if not z:return
  p=aggregate(full_square_shifted(z,m))
  if not any(c<0 for c in p.values()):return
  if initial_target_only and dual is None and not any(c<0 and aggregated.get(e,0)<0 for e,c in p.items()):return
  if dual is not None and sum(float(c)*dual[ix[e]] for e,c in p.items())<1e-9:return
  # Quotient by exact positive scale to remove duplicate rays.
  scale=max(abs(c) for c in p.values());key=tuple((e,c/scale) for e,c in sorted(p.items()))
  if key in seen:return
  seen.add(key);outcols.append(p);outmeta.append([m,[[a,str(c)] for a,c in sorted(z.items())]])
 blocks=[]
 for m in sorted({min(images(m)) for m in exps(d,3)}):
  top=(5-degree(m))//2
  allz=exps(d,top)
  for q in allz:assert evaluate(m+q)>=0,('COUNTEREXAMPLE',tid,m+q,evaluate(m+q))
  # A whole lower box of zeros forces its Newton coefficients to vanish.
  Z=[q for q in allz if any(evaluate(m+r)!=0 for r in lower_box(q))]
  if not Z:continue
  constraints=[[bchoose(q,a) for a in Z] for q in allz if evaluate(m+q)==0]
  constraints=[row for row in constraints if any(row)]
  if degree(m)+2*top==5:
   for S in zeros:
    if support(m)&~S==0:constraints.append([sp.Rational(leading_value(a,S,top)) for a in Z])
  if constraints:
   null=sp.Matrix(constraints).nullspace();TT=sp.Matrix.hstack(*null) if null else sp.zeros(len(Z),0)
  else:TT=sp.eye(len(Z))
  if not TT.cols:continue
  Tnum=np.array(TT,dtype=float);Texact=[[F(TT[i,j]) for j in range(TT.cols)] for i in range(TT.rows)]
  basis=[{a:Texact[i][j] for i,a in enumerate(Z) if Texact[i][j]} for j in range(TT.cols)]
  for z in basis:append_ray(m,z,cols,metadata)
  for a,b in itertools.combinations(basis,2):
   for u,v in ((1,1),(1,2),(2,1)):
    z={e:u*c for e,c in a.items()}
    for e,c in b.items():z[e]=z.get(e,F(0))-v*c
    append_ray(m,z,cols,metadata)
  rr=[];cc=[];vv=[]
  for i,a in enumerate(Z):
   for j,b in enumerate(Z):
    for e,c in aggregate(dict(product3(a,b,m))).items():rr.append(i*len(Z)+j);cc.append(ix[e]);vv.append(float(c))
  moment=csc_matrix((vv,(rr,cc)),shape=(len(Z)**2,len(E)));blocks.append((m,Z,moment,Tnum,Texact))
 print('START',tid,'rows',len(E),'initial_rays',len(cols),'blocks',len(blocks),'zero_directions',len(zeros),'seconds',time.time()-start,flush=True)
 A=sparse_columns(cols);certificate=None
 for iteration in range(iterations):
  sol=linprog(np.r_[np.zeros(len(cols)),np.ones(len(E))],A_ub=hstack([A,-eye(len(E))],format='csc'),b_ub=val,bounds=(0,None),method=lp_method,options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9,'time_limit':120})
  if not sol.success:
   print('LP primary failure',sol.message,flush=True)
   for method,presolve,tol in [('highs-ipm',True,1e-9),('highs-ds',False,1e-8),('highs-ipm',False,1e-8),('highs',True,1e-7)]:
    sol=linprog(np.r_[np.zeros(len(cols)),np.ones(len(E))],A_ub=hstack([A,-eye(len(E))],format='csc'),b_ub=val,bounds=(0,None),method=method,options={'dual_feasibility_tolerance':tol,'primal_feasibility_tolerance':tol,'presolve':presolve,'time_limit':120})
    print('LP fallback',method,presolve,tol,sol.success,sol.message,flush=True)
    if sol.success:break
   if not sol.success:break
  print('iteration',iteration,'objective',sol.fun,'rays',len(cols),'seconds',time.time()-start,flush=True)
  if sol.fun<1e-6:
   exact=None
   for bound in (10**6,10**9,10**12):
    rem={e:F(c) for e,c in aggregated.items()};weights=[]
    for j,value in enumerate(sol.x[:len(cols)]):
     if value<1e-10:continue
     w=F(float(value)).limit_denominator(bound)
     for e,c in cols[j].items():rem[e]=rem.get(e,F(0))-w*c
     weights.append([j,w])
    if all(c>=0 for c in rem.values()):exact=weights;break
   if exact is None:
    used=[j for j,value in enumerate(sol.x[:len(cols)]) if value>1e-8];res=val-A@sol.x[:len(cols)];tight=[i for i,v in enumerate(res) if v<=1e-7]
    print('Exact tight system',len(tight),len(used),flush=True)
    M=sp.Matrix([[sp.Rational(cols[j].get(E[i],0)) for j in used] for i in tight]);rhs=sp.Matrix([aggregated.get(E[i],0) for i in tight])
    try:
     ww=exact_gmp_solve(M,rhs)
     if all(w>=0 for w in ww):
      candidate=[[j,F(w)] for j,w in zip(used,ww) if w];check={e:F(c) for e,c in aggregated.items()}
      for j,w in candidate:
       for e,c in cols[j].items():check[e]=check.get(e,F(0))-w*c
      if all(c>=0 for c in check.values()):exact=candidate
    except Exception as error:print('exact solve',str(error),flush=True)
   if exact is not None:
    rem={e:F(c) for e,c in target.items()};terms=[]
    for j,w in exact:
     m,z=metadata[j];z={a:F(c) for a,c in z};ordinary=shifted_to_ordinary(z,m);poly=full_square_ordinary(ordinary,m)
     assert poly==full_square_shifted(z,m)
     for e,c in poly.items():
      for image in images(e):rem[image]=rem.get(image,F(0))-w*c/len(actions)
     terms.append([str(w),[m,[[a,str(c)] for a,c in sorted(ordinary.items())]]])
    assert all(c>=0 for c in rem.values())
    certificate={'squares':terms,'positive_binomial_remainder':[[e,str(c)] for e,c in sorted(rem.items()) if c]};break
  dual=sol.ineqlin.marginals;new=[];newmeta=[]
  for m,Z,moment,Tnum,Texact in blocks:
   matrix=Tnum.T@np.asarray(moment@dual).reshape(len(Z),len(Z))@Tnum;eigen,vecs=np.linalg.eigh(matrix)
   for j in np.argsort(eigen)[-3:]:
    if eigen[j]<1e-8:continue
    vec=vecs[:,j];vec=vec/max(abs(vec))
    for denominator in(1,2,3,4,8,16,32):
     coordinates=[F(float(v)).limit_denominator(denominator) for v in vec];z={a:sum((x*y for x,y in zip(row,coordinates)),F(0)) for a,row in zip(Z,Texact)}
     append_ray(m,z,new,newmeta,dual)
  print('pricing',iteration,'new_columns',len(new),'seconds',time.time()-start,flush=True)
  if not new:print('NO NEW COLUMNS',flush=True);break
  if prune_columns:
   keep=[j for j,w in enumerate(sol.x[:len(cols)]) if w>0]
   cols=[cols[j] for j in keep];metadata=[metadata[j] for j in keep]
   cols.extend(new);metadata.extend(newmeta)
   seen=set()
   for p in cols:
    scale=max(abs(v) for v in p.values());seen.add(tuple((e,c/scale) for e,c in sorted(p.items())))
   A=sparse_columns(cols)
   print('retained_master_columns',len(cols),flush=True)
  else:
   A=hstack([A,sparse_columns(new)],format='csc');cols.extend(new);metadata.extend(newmeta)
 record={'template':tid,'target':'core_correction_E','certificate':certificate,'seconds':time.time()-start,'solver':'shifted-binomial-square with zero-aware basis'}
 (D/f'global_integer_coreE_pruned_{tid}.json').write_text(json.dumps(record,separators=(',',':'))+'\n')
 print('COMPLETE',tid,'PASS',certificate is not None,'seconds',time.time()-start,flush=True)

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('ids',type=int,nargs='*',default=[5,12,2]);parser.add_argument('--iterations',type=int,default=150);parser.add_argument('--initial-target-only',action='store_true');parser.add_argument('--lp-method',default='highs');parser.add_argument('--prune-columns',action='store_true');args=parser.parse_args()
 for tid in args.ids:main(tid,args.iterations,args.initial_target_only,args.lp_method,args.prune_columns)
