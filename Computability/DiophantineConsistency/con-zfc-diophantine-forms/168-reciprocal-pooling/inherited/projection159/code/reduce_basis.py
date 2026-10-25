from reduce_radical import *
def dot(a,b):
 if len(a)>len(b):a,b=b,a
 return sum(c*b.get(m,0) for m,c in a.items())
def reduce_basis(eq,max_steps=1500,sparse=False):
 rows=[norm(r['terms']) for r in eq['residuals']];ns=[dot(r,r) for r in rows];ops=[]
 for count in range(max_steps):
  best=None
  for i,p in enumerate(rows):
   for j,q in enumerate(rows):
    if i==j or not ns[j]:continue
    d=dot(p,q);k=(2*d+ns[j])//(2*ns[j]);gain=2*k*d-k*k*ns[j]
    if k and gain>0:
     if sparse and len(add(p,scale(q,-k)))>len(p):continue
     candidate=(gain,-abs(k),-i,-j,k)
     if best is None or candidate>best:best=candidate
  if best is None:break
  gain,_,ni,nj,k=best;i=-ni;j=-nj;rows[i]=add(rows[i],scale(rows[j],-k));ns[i]=dot(rows[i],rows[i]);ops.append([i,j,-k])
  if count%50==0:print('row steps',count+1,'norm',sum(ns),flush=True)
 e=copy.deepcopy(eq);e['variant']+=':integer_row_reduction';e['residuals']=[dict(r,terms=terms(p)) for r,p in zip(e['residuals'],rows)]
 return e,{'schema':'integer_row_operations_v1','input_sha256':digest(eq),'operations':ops,'output_sha256':digest(e)}
if __name__=='__main__':
 inp=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True);e=json.loads(inp.read_text());eq,cert=reduce_basis(e,sparse="--sparse" in sys.argv)
 for name,o in [('equation.json',eq),('row_certificate.json',cert),('metrics.json',metric(eq,True))]:(out/name).write_bytes(canonical(o))
 pp=add(*(mul(norm(r['terms']),norm(r['terms'])) for r in eq['residuals']));(out/'expanded_polynomial.json').write_bytes(canonical({'schema':'sparse_integer_polynomial_v1','variables':len(eq['variables']),'terms':terms(pp)}))
 print('done',len(cert['operations']),metric(eq,True))

