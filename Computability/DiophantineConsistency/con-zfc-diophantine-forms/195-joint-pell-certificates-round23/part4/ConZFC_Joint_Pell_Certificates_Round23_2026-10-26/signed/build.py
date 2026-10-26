#!/usr/bin/env python3
"""Deterministic semantic deltas, exact integer maps and quartic expansions."""
import json,copy,hashlib,argparse,tempfile
from pathlib import Path
import algebra as A
ROOT=Path(__file__).resolve().parent
SOURCE='incoming210/equations/principal210/equation.json'
SOURCE_SHA='20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a'
def read(p):return json.loads(p.read_text())
def put(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(A.raw(x))
def digest(x):return hashlib.sha256(A.raw(x)).hexdigest()
def sumps(*ps):
 out={}
 for p in ps:out=A.add(out,p)
 return out
def scale(p,k):return {m:c*k for m,c in p.items()if c*k}
def source():
 p=ROOT/SOURCE;A.need(hashlib.sha256(p.read_bytes()).hexdigest()==SOURCE_SHA,'incoming source pin');return read(p)
def semantic(e,m,centered):
 e=copy.deepcopy(e);names={v['name']:i for i,v in enumerate(e['variables'])};V=lambda n:{(names[n],):1};rows=[A.poly(r['terms'])for r in e['residuals']];labels={r['label']:i for i,r in enumerate(e['residuals'])};t,F=V('t0'),V('growth.F');z=names['cofinal.horizon_root'];h=labels['cofinal.horizon'];A.need(rows[h]==sumps(t,{():-16,(z,z):-4}),'old horizon binding');rows[h]=sumps(t,{():-m,(z,):-2*m});cert={'schema':'round23_semantic_source_v1','m':m,'horizon_row':h,'source_sha256':digest(e),'centered':centered};A.need(m in [4,16],'proved horizon minimum')
 if centered:
  C=scale(V('crt.even_index_half'),2);q=sumps(V('pow2.output'),{():-1});D=sumps({():2},scale(F,2),scale(C,2));reps=[V('crt.encoded.'+n)for n in ['a','b','c','d','S','Sp','u','vq']]+[C]
  atoms=[t,sumps(t,{():1}),sumps(F,t),V('x'),t,V('choose0.output'),F,V('beta.y_plus_one')]+reps+[V('pow1.output'),q,V('pow2.output'),D]+[V('pow%d.output'%i)for i in [3,4,5,7,8,9,10,11,12,13,14,15,16]]
  fi=labels['shared.frame_definition'];A.need(rows[fi]==sumps(V('shared.W'),{():-2},*[scale(A.mul(a,a),-1)for a in atoms]),'literal 34-atom frame')
  actual=[A.subst(a,names['t0'],{():m,(z,):2*m})for a in atoms];support=sorted({v for a in actual for mon in a for v in mon});bounds=[abs(a.get((),0))+sum(c*c//4 for mon,c in a.items()if mon)for a in actual];constant=max(bounds)+1;A.need(names['growth.F']in support,'F frame atom retained');A.need(all(len(mon)<=1 for a in actual for mon in a),'affine atom ledger');A.need(len(atoms)==34 and constant==m*m+m+2,'frame arithmetic constant')
  rows[fi]=sumps(V('shared.W'),{():-constant},*[{(v,v):-1}for v in support]);Y0,Y2=V('index0.Y'),V('index2.Y');old=sumps(Y2,scale(t,-1),scale(F,-1));new=sumps(Y2,scale(Y0,-1),scale(F,-1));delta=A.add(A.mul(new,new),A.mul(old,old),-1);oi=labels['cap.pooled_index_residue'];rows[oi]=A.add(rows[oi],delta)
  cert['frame']={'row':fi,'old_atoms':[A.terms(a)for a in atoms],'actual_atoms':[A.terms(a)for a in actual],'bounds':bounds,'constant':constant,'coordinates':support,'maximum_affine_l1':max(sum(map(abs,a.values()))for a in actual)};cert['difference']={'row':oi,'delta':A.terms(delta),'retained_t_error_pair':'index0','difference_pair':'index2'}
 for r,p in zip(e['residuals'],rows):r['terms']=A.terms(p)
 e['variant']='round23_modified_semantic_source';cert['output_sha256']=digest(e);return e,cert

def split(e,exps):
 e=copy.deepcopy(e);cert={'schema':'round23_monic_split_v1','exponents':exps,'definitions':[],'input_sha256':digest(e)}
 if not exps:return e,cert
 A.need(all(type(a)is int and a>=0 for a in exps)and sum(exps)==19,'factor exponents');names={v['name']:i for i,v in enumerate(e['variables'])};t,F,u=[names[n]for n in ['t0','growth.F','growth_pell.odd_half']];rows=[A.poly(r['terms'])for r in e['residuals']];target={(F,):1,(t,):-2**19,tuple(sorted((t,u))):-2**20};matches=[j for j,p in enumerate(rows)if p==target];A.need(len(matches)==1,'growth divisibility row');j=matches[0];last=t
 for k,a in enumerate(exps[:-1]):
  w=len(e['variables']);e['variables'].append({'name':f'growth_pell.split{k}','kind':'unit_defined_wire'});e['residuals'].append({'label':f'growth.split{k}','terms':A.terms({(w,):1,(last,):-2**a})});cert['definitions'].append({'coordinate':w,'previous':last,'factor':2**a,'row':len(e['residuals'])-1});last=w
 a=exps[-1];e['residuals'][j]['terms']=A.terms({(F,):1,(last,):-2**a,tuple(sorted((last,u))):-2**(a+1)});cert.update(row=j,last=last,last_factor=2**a,output_sha256=digest(e));return e,cert

def project(e,m):
 e=copy.deepcopy(e);names={v['name']:i for i,v in enumerate(e['variables'])};t,z=[names[n]for n in ['t0','cofinal.horizon_root']];f={():m,(z,):2*m};rows=[A.poly(r['terms'])for r in e['residuals']];target=A.add({(t,):1},f,-1);matches=[j for j,p in enumerate(rows)if p==target];A.need(len(matches)==1,'linear horizon row');j=matches[0];rows=[A.subst(p,t,f)for i,p in enumerate(rows)if i!=j];keep=[i for i in range(len(e['variables']))if i!=t];live=sorted({i for p in rows for mon in p for i in mon});A.need(live==keep,'only horizon coordinate removed');out=A.compact(e,rows);out['variant']='round23_affine_projection';return out,{'schema':'round23_unit_affine_projection_v1','input_sha256':digest(e),'eliminated_coordinate':t,'deleted_row':j,'replacement':A.terms(f),'retained_indices':keep,'output_sha256':digest(out)}

def build_endpoint(name,desc):
 e,semantic_cert=semantic(source(),desc['m'],desc['centered']);unsplit=copy.deepcopy(e);e,split_cert=split(e,desc.get('split',[]));modified=copy.deepcopy(e);e,projection=project(e,desc['m']);operations=read(ROOT/desc['row_certificate'])['operations']if desc.get('row_certificate')else[];rows=[A.poly(r['terms'])for r in e['residuals']]
 for i,j,k in operations:A.need(type(k)is int and i!=j and 0<=i<len(rows)and 0<=j<len(rows),'integer invertible row step');rows[i]=A.add(rows[i],rows[j],k)
 for r,p in zip(e['residuals'],rows):r['terms']=A.terms(p)
 e['variant']='round23:'+name;expanded,metrics=A.result(e);cert={'semantic':semantic_cert,'split':split_cert,'projection':projection,'row_operations':operations,'output_sha256':digest(e)};return e,expanded,metrics,cert,modified,unsplit

def run(out):
 for name,desc in read(ROOT/'ENDPOINTS.json').items():
  e,p,m,c,s,u=build_endpoint(name,desc)
  for file,x in [('equation.json',e),('expanded_polynomial.json',p),('metrics.json',m),('certificate.json',c),('modified_source.json',s),('unsplit_modified_source.json',u)]:put(out/name/file,x)
 # Exact source bytes required by the separately calibrated reciprocal branch.
 old=source();names={v['name']:i for i,v in enumerate(old['variables'])};t,z=names['t0'],names['cofinal.horizon_root'];rows=[A.poly(r['terms'])for r in old['residuals']];h=[i for i,r in enumerate(old['residuals'])if r['label']=='cofinal.horizon'][0];rows=[A.subst(p,t,{():16,(z,):32})for i,p in enumerate(rows)if i!=h];conservative=A.compact(old,rows);conservative['variant']=old.get('variant','')+':signed_affine_horizon_m16';put(out/'conservative209/equation.json',conservative);A.need(digest(conservative)=='27eec42f8010ef84ed427a0e78c1f7ffe2c5bd1baf712d87cfb0f18f23dd4d63','reciprocal source byte identity')
 return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);ap.add_argument('--check',action='store_true');args=ap.parse_args()
 if args.check:
  with tempfile.TemporaryDirectory(prefix='round23-signed-')as td:
   out=run(Path(td));files=[]
   for p in sorted(out.rglob('*.json')):
    rel=p.relative_to(out);A.need(p.read_bytes()==(ROOT/rel).read_bytes(),'reconstruction '+str(rel));files.append(str(rel))
   print(json.dumps({'status':'PASS','reconstructed_files':files},indent=2))
 else:run(args.output or ROOT)
if __name__=='__main__':main()
