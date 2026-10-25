#!/usr/bin/env python3
"""Independent literal source-change audit. Imports no producer."""
import argparse,copy,hashlib,json
from pathlib import Path

def need(p,message):
 if not p:raise ValueError(message)
def canonical(p):return {tuple(m):c for c,m in p}
def verify(root,final=None):
 d=root/'sources';cert=json.loads((d/'odd_square_composition_certificate.json').read_text());raw=(d/'common_remainders252.json').read_bytes();old=json.loads(raw)
 need(hashlib.sha256(raw).hexdigest()==cert['source_sha256'],'source pin')
 if final is None:final=json.loads((d/'common_remainders250_odd.json').read_text())
 names={v['name']:i for i,v in enumerate(old['variables'])};q=names['pow2.output'];B=names['choose0.output'];deleted={names['new_guard2.'+s] for s in 'abc'};a,b,c=sorted(deleted)
 rows=[i for i,r in enumerate(old['residuals']) if r['label']=='domain_guard.2'];need(rows==[179],'exact unique guard row')
 expected={():-2,(B,):-1,(q,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}
 need(canonical(old['residuals'][179]['terms'])==expected,'q-B-1 ternary guard shape')
 need(all(not(deleted&set(m)) for i,r in enumerate(old['residuals']) if i!=179 for _,m in r['terms']),'three private guard witnesses')
 keep=[i for i in range(253) if i not in deleted];rename={v:i for i,v in enumerate(keep)}
 need(cert['removed_coordinates']==sorted(deleted) and cert['retained_extended_coordinates']==keep,'certificate coordinates')
 expected_vars=[old['variables'][i] if i<252 else {'name':'radix.odd_square_root','kind':'signed_witness'} for i in keep]
 need(final['variables']==expected_vars and len(expected_vars)==250,'exact output variables')
 need(len(final['residuals'])==182,'row count')
 for i,r in enumerate(old['residuals']):
  if i==179:
   want={():-2,(rename[q],):1,(rename[252],):-4,(rename[252],rename[252]):-4};label='radix.odd_square'
  else:
   want={tuple(rename[v] for v in m):c for c,m in r['terms']};label=r['label']
  need(final['residuals'][i]['label']==label and canonical(final['residuals'][i]['terms'])==want,'untouched row or odd square identity '+str(i))
 need(final['domain']==old['domain']=='unrestricted integers','integer domain')
 need({v for r in final['residuals'] for _,m in r['terms'] for v in m}==set(range(250)),'liveness')
 return {'status':'pass','old_variables':252,'new_variables':250,'rows':182,'unchanged_rows_after_exact_renumbering':181,'private_coordinates_removed':sorted(deleted),'radix_identity':'q=x107-1=(2z+1)^2','scope':'Finite edit only. Zero-existence equivalence uses ODD_SQUARE_COMPOSITION_PROOF.md.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--release',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--output',type=Path);a=p.parse_args();result=verify(a.release);out=json.loads((a.release/'sources/common_remainders250_odd.json').read_text());bad=copy.deepcopy(out);bad['residuals'][179]['terms'][0][0]+=1
 try:verify(a.release,bad)
 except ValueError:result['odd_square_corruption_rejected']=True
 else:raise ValueError('accepted corrupted odd square')
 bad=copy.deepcopy(out);bad['residuals'][0]['terms'][0][0]+=1
 try:verify(a.release,bad)
 except ValueError:result['untouched_row_corruption_rejected']=True
 else:raise ValueError('accepted corrupted untouched row')
 result['optimized_python']=not __debug__;text=json.dumps(result,indent=2)+'\n'
 if a.output:a.output.write_text(text)
 print(text,end='')
