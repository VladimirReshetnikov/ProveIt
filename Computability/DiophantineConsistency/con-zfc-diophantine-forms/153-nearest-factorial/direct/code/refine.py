#!/usr/bin/env python3
import argparse,copy,json,sys,pathlib,hashlib
from collections import defaultdict
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
import terminal_elimination as E
from factor_horn import add,V
from affine import kernels

def dump(p,x):p.write_bytes(E.canonical_bytes(x))
def scale(r,k):return {m:c*k for m,c in r.items() if c*k}
def objective(r,penalty):return sum(c*c for c in r.values())+penalty*len(r)
def row_reduce(rows,penalty=0,maxsteps=1000):
 ops=[]
 for step in range(maxsteps):
  best=None
  for i,a in enumerate(rows):
   oa=objective(a,penalty)
   for j,b in enumerate(rows):
    if i==j:continue
    dot=sum(c*b.get(m,0) for m,c in a.items());norm=sum(c*c for c in b.values())
    if not dot or not norm:continue
    n=(-dot)//norm
    for k in {n,n+1,-1 if dot>0 else 1}:
     if not k:continue
     c=add(a,scale(b,k));oc=objective(c,penalty)
     if oc>=oa:continue
     score=(oc-oa,len(c)-len(a),i,j,k)
     if best is None or score<best[0]:best=(score,i,j,k,c)
  if best is None:break
  _,i,j,k,c=best;rows[i]=c;ops.append([i,j,k])
 return ops

def build(inp,out,cap=16,penalty=0):
 out.mkdir(parents=True,exist_ok=True)
 src=json.loads(inp.read_text());e=copy.deepcopy(src);names={v['name']:i for i,v in enumerate(e['variables'])}
 rows=[E.normalize(r['terms']) for r in e['residuals']]
 shears=[['mul.40',{'crt.encoded.a':-2,'crt.encoded.b':-2}],['mul.53',{'add.50':-8}],['mul.148',{'add.145':-8}],['mul.137',{'crt.encoded.a':-4,'crt.encoded.c':-5,'mul.64':-2,'mul.75':-1}],['mul.75',{'crt.encoded.a':-1,'crt.encoded.c':-1}],['mul.64',{'crt.encoded.b':-1,'crt.encoded.c':-1}]]
 for target,d in shears:
  repl=add(V(names[target]),{(names[k],):v for k,v in d.items()});rows=[E.substitute(r,names[target],repl) for r in rows]
 ks=kernels(rows);ops=[]
 for k in ks:
  target=max(k)
  if k[target]!=1:raise ValueError('nonunit kernel pivot')
  for j,a in sorted(k.items()):
   if j!=target:
    rows[target]=add(rows[target],scale(rows[j],a));ops.append([target,j,a])
  if E.degree(rows[target])>1:raise ValueError('not affine')
 exposed=copy.deepcopy(e)
 exposed['residuals']=[dict(r,terms=E.as_terms(p)) for r,p in zip(e['residuals'],rows)]
 projected,pc,metrics=E.optimize(exposed,max_support=cap,affine_support=cap)
 E.verify(exposed,projected,pc)
 rr=[E.normalize(r['terms']) for r in projected['residuals']]
 rops=row_reduce(rr,penalty)
 eq=copy.deepcopy(projected);eq['variant']+=':row_exposure_reduced';eq['residuals']=[dict(r,terms=E.as_terms(p)) for r,p in zip(projected['residuals'],rr)]
 p=E.expand(eq)
 metrics={'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':max(len(m) for c,m in p['terms']),'monomials':len(p['terms']),'height':max(abs(c) for c,m in p['terms']),'row_height':max(abs(c) for r in rr for c in r.values()),'row_operations':len(rops),'projection_count':len(pc['steps'])}
 eq['metrics']=dict(metrics)
 eq.pop('elimination',None)
 eq['refinement_certificate']='certificate.json'
 shear_targets={t for t,d in shears}
 eq['variables']=[{'name':'x'+str(i),'source_name':v['name'],'source_kind':v.get('kind'),'source_coordinate':pc['retained_original_variables'][i],'coordinate_was_sheared':v['name'] in shear_targets} for i,v in enumerate(projected['variables'])]
 cert={'source_sha256':hashlib.sha256(E.canonical_bytes(src)).hexdigest(),'coordinate_shears':shears,'exposure_operations':ops,'final_operations':rops,'penalty':penalty,'cap':cap}
 for name,obj in [('source.json',src),('exposed.json',exposed),('projected.json',projected),('projection_certificate.json',pc),('certificate.json',cert),('equation.json',eq),('expanded_polynomial.json',p),('METRICS.json',metrics)]:dump(out/name,obj)
 print(json.dumps(metrics))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('input',type=pathlib.Path);p.add_argument('out',type=pathlib.Path);p.add_argument('--cap',type=int,default=16);p.add_argument('--penalty',type=int,default=100);a=p.parse_args();build(a.input,a.out,a.cap,a.penalty)
