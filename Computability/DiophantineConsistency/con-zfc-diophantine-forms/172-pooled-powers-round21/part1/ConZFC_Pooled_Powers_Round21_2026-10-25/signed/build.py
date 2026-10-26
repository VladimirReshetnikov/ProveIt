#!/usr/bin/env python3
"""Deterministic finite reconstruction of the three Round21 signed quartics."""
import argparse,copy,hashlib,json,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import operations as O,basis,build_pools,shear_pell,reduce_radical as R,affine_project as AP

def read(p):return json.loads(p.read_text())
def put(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(O.raw(x))
def checks():
 for rel,sha in read(ROOT/'SOURCE_PINS.json').items():O.need(hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==sha,'source pin '+rel)
def beta(e):
 names={v['name']:i for i,v in enumerate(e['variables'])};u=names['beta.odd_square_multiplier'];v=names['beta.odd_square_root_half'];rows=[O.poly(r['terms'])for r in e['residuals']];j=next(j for j,r in enumerate(e['residuals'])if r['label']=='beta.odd_square_multiplier')
 O.need(rows[j]=={():-1,(u,):1,(v,):-4,(v,v):-4},'beta source');rows[j]={():-1,(u,):1,(v,):-2};rows=[O.subst(p,u,{():1,(v,):2})for p in rows];new=O.compact(e,rows)
 for r,label in zip(new['residuals'],[r['label']for k,r in enumerate(e['residuals'])if k!=j]):r['label']=label
 return new
def sphere(e):
 e=copy.deepcopy(e);found=0
 for r in e['residuals']:
  if r['label']=='domain_guard.4':
   found+=1;O.need(sum(c==-4 for c,m in r['terms'])==11 and [-1,[]] in r['terms'],'norm source');r['terms']=[[(-2 if c==-4 else c),m]for c,m in r['terms']]
 O.need(found==1,'single norm');return e
def row_reduce(e,cert):
 O.need(R.digest(e)==cert['input_sha256'],'row source');new=copy.deepcopy(e);rs=[O.poly(r['terms'])for r in e['residuals']]
 for i,j,k in cert['operations']:O.need(i!=j,'row distinct');rs[i]=O.add(rs[i],rs[j],k)
 for r,p in zip(new['residuals'],rs):r['terms']=O.terms(p)
 new['variant']+=':integer_row_reduction';O.need(R.digest(new)==cert['output_sha256'],'row target');return new

def run(out):
 source=read(ROOT/'inherited_strict/direct/source/equation.json');e=basis.build(source,read(ROOT/'certificates/basis236.json'));put(out/'stages/basis236/equation.json',e)
 build_pools.main(out/'stages/basis236/equation.json',out/'stages/pooled224')
 shear_pell.main(out/'stages/pooled224/equation.json',out/'stages/differences224')
 e=beta(read(out/'stages/differences224/equation.json'));put(out/'stages/beta223/equation.json',e);e=sphere(e)
 for ops in read(ROOT/'stages/core219/operations.json'):e=O.stage(e,ops)
 put(out/'stages/core219/equation.json',e)
 for cert in read(ROOT/'stages/radical217/projection_certificate.json')['steps']:
  v=[0]*len(e['variables'])
  for i,c in cert['direction']:v[i]=c
  e,actual=R.project(e,v,cert['pivot'],cert['deleted_row']);O.need(actual==cert,'radical certificate')
 put(out/'stages/radical217/equation.json',e);radical=e
 for name in read(ROOT/'ENDPOINTS.json'):
  source=radical
  if name=='dimension216':
   cert=read(ROOT/'stages/affine216/projection_certificate.json');source,actual=AP.project(source,cert['affine_consequence'],cert['eliminated_coordinate']);put(out/'stages/affine216/equation.json',source)
  result=row_reduce(source,read(ROOT/name/'row_certificate.json'));put(out/name/'equation.json',result);exp,met=O.result(result)
  # Public expansion retains the canonical generic quadratic-projection schema.
  exp={'schema':'sparse_integer_polynomial_v1','variables':len(result['variables']),'terms':exp['terms']};met=R.metric(result,True)
  put(out/name/'expanded_polynomial.json',exp);put(out/name/'metrics.json',met)
 return out

def main():
 a=argparse.ArgumentParser();a.add_argument('--output',type=Path);a.add_argument('--check',action='store_true');args=a.parse_args();checks()
 if args.check:
  with tempfile.TemporaryDirectory(prefix='round21-signed-')as td:
   p=run(Path(td));count=0
   for f in p.rglob('*.json'):
    rel=f.relative_to(p);target=ROOT/rel
    if target.exists():
     # The affine intermediate author formatting is noncanonical; compare exact objects there only.
     if str(rel)=='stages/affine216/equation.json':O.need(read(f)==read(target),'affine intermediate')
     else:O.need(f.read_bytes()==target.read_bytes(),'rebuild '+str(rel))
     count+=1
   print(json.dumps({'status':'PASS','reconstructed_json_files':count,'endpoints':read(ROOT/'ENDPOINTS.json')}))
 else:run(args.output or ROOT)
if __name__=='__main__':main()
