#!/usr/bin/env python3
"""Deterministic mod-four signed-radix semantic edit plus monic projection.
The semantic zero-existence equivalence is proved in PROOF.md, not by this builder.
"""
import argparse,copy,hashlib,json
from collections import defaultdict
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def data(p):return json.loads(p.read_text())
def enc(o):return (json.dumps(o,sort_keys=True,separators=(',',':'))+'\n').encode()
def write(p,o):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(enc(o))
def normalized(ts):
 d=defaultdict(int)
 for c,m in ts:d[tuple(sorted(m))]+=c
 return {m:c for m,c in d.items()if c}
def terms(p):return [[c,list(m)]for m,c in sorted(p.items())if c]
def product(p,q):
 d=defaultdict(int)
 for m,c in p.items():
  for n,v in q.items():d[tuple(sorted(m+n))]+=c*v
 return {m:c for m,c in d.items()if c}
def replace(p,i,q):
 d=defaultdict(int)
 for m,c in p.items():
  t={():c}
  for j in m:t=product(t,q if j==i else {(j,):1})
  for n,v in t.items():d[n]+=v
 return {m:c for m,c in d.items()if c}
def measure(eq):
 s=defaultdict(int)
 for r in eq['residuals']:
  p=normalized(r['terms'])
  for m,c in product(p,p).items():s[m]+=c
 s={m:c for m,c in s.items()if c}
 return {'schema':'expanded_integer_polynomial_v1','domain':'unrestricted integers','variables':len(eq['variables']),'terms':terms(s)}, {'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':max(map(len,s)),'monomials':len(s),'height':max(map(abs,s.values())),'row_height':max(abs(c)for r in eq['residuals']for c,m in r['terms'])}
def construct(source,old,offset=2,linear_radius=False):
 names={v['name']:i for i,v in enumerate(old['variables'])};q=names['pow2.output'];z=names['radix.odd_square_root_half']
 hits=[i for i,r in enumerate(old['residuals'])if r['label']=='radix.odd_square']
 if len(hits)!=1:raise ValueError('radix guard not unique')
 i=hits[0];before={():-2,(q,):1,(z,):-4,(z,z):-4}
 if normalized(old['residuals'][i]['terms'])!=before:raise ValueError('literal actual q = stored q minus one')
 if offset%4!=2:raise ValueError('actual radix must be one modulo four')
 replacement={():offset,(z,):4}
 f=names['crt.growth_majorant_F'];r=names['mul.1']
 radius_guard={tuple(m):c for c,m in old['residuals'][0]['terms']}
 if radius_guard!={(f,f):-1,(r,):1}:raise ValueError('literal R=F^2 guard')
 removed={q,r} if linear_radius else {q}
 keep=[v for v in range(len(old['variables']))if v not in removed];rename={v:j for j,v in enumerate(keep)}
 eq=copy.deepcopy(old);eq['variant']='factorial_free_'+('linear_radius_' if linear_radius else '')+'mod_four_radix_'+str(len(keep));eq['variables']=[old['variables'][v]for v in keep]
 eq['variables'][rename[z]]={'name':'radix.mod_four_parameter','kind':'unrestricted_integer'}
 rows=[]
 for j,r in enumerate(old['residuals']):
  if j==i or (linear_radius and j==0):continue
  p=replace(normalized(r['terms']),q,replacement)
  if linear_radius:p=replace(p,names['mul.1'],{(f,):1})
  rows.append(dict(r,terms=terms({tuple(rename[v]for v in m):c for m,c in p.items()})))
 eq['residuals']=rows
 cert={'schema':'semantic_radix_mod_four_v1','source_file':source.name,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
  'actual_radix':[[1,[q]],[-1,[]]],'source_guard_row':i,'old_guard':old['residuals'][i],
  'edited_guard':{'label':'radix.mod_four','terms':terms({(q,):1,(z,):-4,():-offset})},
  'retained_source_coordinates':keep,'deleted_coordinate':q,'retained_parameter':z,'linear_radius':linear_radius,'radius_coordinate':names['mul.1'],'majorant_coordinate':f,'stored_q_replacement':terms(replacement),
  'old_to_edited_parameter':terms({(z,z):1,(z,):1,():(2-offset)//4}),
  'zero_set_claim':'The source edit preserves zero existence by the ordinary proof; it is not a bijection of complete witness tuples.',
  'projection_claim':'The edited system and endpoint have inverse restriction/restoration maps.'}
 if linear_radius:cert['radius_edit']={'row':0,'old':old['residuals'][0],'new':{'label':'radius.linear_majorant','terms':terms({(names['mul.1'],):1,(f,):-1})}}
 restored=[]
 for v in range(len(old['variables'])):
  r=replacement if v==q else {(f,):1} if linear_radius and v==names['mul.1'] else {(v,):1}
  restored.append(terms({tuple(rename[w]for w in m):c for m,c in r.items()}))
 restoration={'schema':'affine_projection_restoration_v1','target':'edited source, not original odd-square source','coordinates':restored,'dropped_residual':i,'radius_dropped_residual':0 if linear_radius else None}
 return eq,cert,restoration

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=ROOT);ap.add_argument('--offset',type=int,default=2);a=ap.parse_args()
 for oldn,linear in [(241,False),(242,False),(241,True),(242,True)]:
  source=ROOT/'sources'/('factorial_free'+str(oldn)+'.json');old=data(source)
  eq,cert,rest=construct(source,old,a.offset,linear);poly,met=measure(eq);out=a.out/(('linear_' if linear else 'mod4_')+'integer'+str(oldn-1-int(linear)))
  for f,o in [('equation.json',eq),('expanded_polynomial.json',poly),('METRICS.json',met),('certificate.json',cert),('RESTORATION.json',rest)]:write(out/f,o)
  print(out.name,json.dumps(met,sort_keys=True))
if __name__=='__main__':main()
