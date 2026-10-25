"""Unimodular Pell difference coordinates, with a certified residual row edit."""
from pathlib import Path
import json,copy,hashlib,argparse
from collections import defaultdict

def add(*ps):
 d=defaultdict(int)
 for p in ps:
  for m,c in p.items():d[m]+=c
 return {m:c for m,c in d.items() if c}
def mul(p,q):
 d=defaultdict(int)
 for m,c in p.items():
  for n,b in q.items():d[tuple(sorted(m+n))]+=c*b
 return {m:c for m,c in d.items() if c}
def scale(k,p):return {m:k*c for m,c in p.items() if k*c}
def v(i):return {(i,):1}
def c(i):return {():i} if i else {}
def sub(p,q):return add(p,scale(-1,q))
def subst(p,maps):
 out={}
 for mon,coef in p.items():
  term=c(coef)
  for i in mon:term=mul(term,maps.get(i,v(i)))
  out=add(out,term)
 return out
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]
def main(parent,out):
 raw=parent.read_bytes();a=json.loads(raw);names={z['name']:i for i,z in enumerate(a['variables'])};rows=[{tuple(m):coef for coef,m in r['terms']} for r in a['residuals']];variables=copy.deepcopy(a['variables']);maps={};normsum={};norm_records=[]
 pairs=[(0,'mul.460',0,0),(2,'mul.503',0,0),(3,'mul.529',-1,0),(5,'mul.554',0,0),(6,'mul.567',0,0),(7,'mul.580',0,0),(8,'mul.593',0,0),(9,'mul.606',0,0),(10,'mul.619',0,0),(11,'mul.632',0,0),(12,'mul.645',0,1),(13,'mul.658',0,0),(14,'mul.671',0,0),(15,'mul.684',0,0)]
 for ino,zname,yshift,zshift in pairs:
  xi=names[f'index{ino}.X'];yi=names[f'index{ino}.Y'];zi=names[zname];X=add(v(xi),c(1));Y=add(v(yi),c(yshift));Z=add(v(zi),c(zshift));N=add(mul(X,X),mul(Y,Y),scale(-1,mul(Z,Z)),c(-1))
  hits=[(j,1 if r==N else -1) for j,r in enumerate(rows) if r==N or r==scale(-1,N)]
  if len(hits)!=1:raise ValueError(('norm not found',ino,hits))
  normsum=add(normsum,N);norm_records.append([ino,hits[0][0],hits[0][1]])
  # actual old X = new D + actual Z; stored old X=actual oldX−1.
  maps[xi]=add(v(xi),Z,c(-1));variables[xi]={'kind':'pell_difference','name':f'index{ino}.X_minus_AY'}
 qi=names['cap.pooled_quotient'];hits=[j for j,r in enumerate(rows) if any(qi in m for m in r)]
 if len(hits)!=1:raise ValueError('orientation row not unique')
 idx=hits[0];oldrow=rows[idx];rows[idx]=sub(rows[idx],normsum)
 newrows=[subst(r,maps) for r in rows]
 if any(len(m)>2 for r in newrows for m in r):raise ValueError('degree invariant failed')
 inverse={i:sub(scale(2,v(i)),p) for i,p in maps.items()}
 for old,new in zip(rows,newrows):
  if subst(new,inverse)!=old:raise ValueError('inverse affine map failed')
 eq=dict(a,variables=variables,residuals=[{'label':r['label'],'terms':terms(p)} for r,p in zip(a['residuals'],newrows)],schema='conzfc-pell-difference-v1',variant='pell_difference',parent_equation_sha256=hashlib.sha256(raw).hexdigest())
 ex={}
 for r in newrows:ex=add(ex,mul(r,r))
 met={'variables':len(variables),'rows':len(newrows),'degree':max(map(len,ex)),'monomials':len(ex),'height':max(map(abs,ex.values())),'row_height':max(abs(x) for r in newrows for x in r.values())}
 cert={'schema':'pell_difference_certificate_v1','parent_equation_sha256':hashlib.sha256(raw).hexdigest(),'orientation_row':idx,'orientation_parent_terms':terms(oldrow),'norm_subtractions':norm_records,'old_in_new':[[i,terms(p)] for i,p in maps.items()],'new_in_old':[[i,terms(p)] for i,p in inverse.items()]}
 out.mkdir(parents=True,exist_ok=True)
 for fn,obj in [('equation.json',eq),('expanded_polynomial.json',{'schema':'sparse-polynomial-v1','domain':'unrestricted integers','variables':len(variables),'terms':terms(ex)}),('METRICS.json',met),('shear_certificate.json',cert)]:
  (out/fn).write_text(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n')
 print(json.dumps(met))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();main(a.parent,a.output)
