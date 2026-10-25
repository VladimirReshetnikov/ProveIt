#!/usr/bin/env python3
"""Data-only check that radius row0 and its coordinates survive the prior compiler.
Does not import or execute the external producer. Full prior algebra replay is
separately available in inherited_factorial_free/verify.py.
"""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent;BASE=ROOT/'inherited_factorial_free/direct'
def need(t,s):
 if not t:raise ValueError(s)
def read(p):return json.loads(p.read_text())
def poly(r):return {tuple(m):c for c,m in r['terms']}
def main():
 ledger=read(ROOT/'SOURCE_BINDINGS.json')
 for rel,h in ledger['pins'].items():need(hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==h,'pinned '+rel)
 raw=read(BASE/'factorial_free_affine/raw_source.json');fact=read(BASE/'factorial_free_affine/factored_source.json')
 names={v['name']:i for i,v in enumerate(raw['variables'])};f=names['crt.growth_majorant_F'];r=names['mul.1']
 need(poly(raw['residuals'][0])=={(f,f):-1,(r,):1},'raw radius graph')
 need(fact['residuals'][0]==raw['residuals'][0],'factoring retains radius row')
 fc=read(BASE/'factorial_free_affine/factorization_certificate.json');need(0 not in fc['deleted_rows'] and all(e['row']!=0 for e in fc['changes']),'factoring does not edit row0')
 pc=read(BASE/'factorial_free_affine/projection_certificate.json')
 need(all(e['row_id']!=0 and e['variable']not in[f,r] for e in pc['steps']),'monic projections do not use radius row or remove F,R')
 need(pc['retained_original_rows'][0]==0 and f in pc['retained_original_variables']and r in pc['retained_original_variables'],'row and coordinate retention')
 pr=read(BASE/'factorial_free_affine/projected.json');nn={v['name']:i for i,v in enumerate(pr['variables'])};fp=nn['crt.growth_majorant_F'];rp=nn['mul.1']
 need(poly(pr['residuals'][0])=={(fp,fp):-1,(rp,):1},'projected radius graph')
 tr=read(BASE/'factorial_free_affine/translation_certificate.json')
 need(dict(tr['shifts']).get(fp,0)==0 and dict(tr['shifts']).get(rp,0)==0,'F,R translations zero')
 for n,kind in [(241,'companion'),(242,'principal')]:
  cert=read(BASE/f'factorial_free_affine{n}_balanced/certificate.json')
  need(all(t not in['crt.growth_majorant_F','mul.1']for t,inputs in cert['coordinate_shears']),'F,R not sheared')
  need(all(0 not in[i,j]for i,j,k in cert['row_operations']+cert['final_row_operations']),'row0 not used in row combinations')
  need(all(e['row']!=0 and e['variable']not in[fp,rp]for e in cert['projections']),'last projections preserve radius row')
  eq=read(BASE/kind/'equation.json');need((BASE/kind/'equation.json').read_bytes()==(ROOT/'sources'/f'factorial_free{n}.json').read_bytes(),'immediate endpoint identity')
  names={v['name']:i for i,v in enumerate(eq['variables'])};need(names['crt.growth_majorant_F']==3 and names['mul.1']==4,'endpoint F,R positions')
  need(poly(eq['residuals'][0])=={(3,3):-1,(4,):1},'endpoint radius graph')
 return {'status':'pass','scope':'Pinned data-only interface audit; radius equation can be replaced before or after the retained exact compiler. Prior global transformations have their own inherited checker.','pinned_files':len(ledger['pins']),'F':3,'R':4,'source_row':0,'all_other_source_rows_unchanged':True}
if __name__=='__main__':print(json.dumps(main(),indent=2,sort_keys=True))
