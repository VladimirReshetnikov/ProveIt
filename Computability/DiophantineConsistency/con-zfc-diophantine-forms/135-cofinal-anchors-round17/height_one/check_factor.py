#!/usr/bin/env python3
"""Independent monic-extension check of the affine source refactorization."""
import argparse, hashlib, json, sys
from copy import deepcopy
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
from verify_graph import require,sparse,pullback

def verify(original,source,certificate,digest):
 require(certificate['schema']=='rank-one-affine-refactor-v1','Refactor schema')
 require(certificate['source_sha256']==digest,'Original hash')
 n=len(original['variables']); m=len(source['variables']); d=m-n
 require(n==certificate['original_variables'] and d==certificate['definition_rows']==certificate['row_offset'],'Dimensions')
 require(source['domain']==original['domain']=='unrestricted integers','Domains')
 require(source['variables'][:n]==original['variables'],'Original variable metadata')
 require(len(source['residuals'])==d+len(original['residuals']),'Row count')
 substitutions=[{(i,):1} for i in range(n)]
 for j,row in enumerate(source['residuals'][:d]):
  pivot=n+j; terms=sparse(row['terms'],m)
  require(terms.get((pivot,))==1,'Monic constructor')
  require(all(len(mon)<=1 and (not mon or mon[0]<=pivot) for mon in terms),'Topological affine constructor')
  rhs=[[-c,list(mon)] for mon,c in terms.items() if mon!=(pivot,)]
  substitutions.append(pullback(rhs,substitutions))
  require(not pullback(row['terms'],substitutions),'Constructor zero pullback')
 for i,(a,b) in enumerate(zip(original['residuals'],source['residuals'][d:])):
  require(a['label']==b['label'],'Source row order')
  require(pullback(b['terms'],substitutions)==sparse(a['terms'],n),'Exact source row pullback')
 records=certificate['records']; seen=set(); used_pivots=set()
 for rec in records:
  r=rec['source_row']; z=rec['pivot']
  require(type(r) is int and 0<=r<len(original['residuals']) and r not in seen,'Refactor row ledger'); seen.add(r)
  require(type(z) is int and n<=z<m,'Refactor pivot'); used_pivots.add(z)
  require(sparse(rec['affine'],n)==substitutions[z],'Affine factor ledger')
  require(rec['sign'] in (-1,1),'Factor sign')
  actual=sparse(source['residuals'][d+r]['terms'],m)
  require(actual.get((z,z))==rec['sign'],'Factor square occurrence')
 require(used_pivots==set(range(n,m)),'All factor pivots recorded')
 for r in set(range(len(original['residuals'])))-seen:
  require(source['residuals'][d+r]==original['residuals'][r],'Unchanged row ledger')
 return {'original_variables':n,'refactored_variables':m,'monic_definitions':d,'refactored_rows':len(records),'row_pullbacks':len(original['residuals'])}

def main():
 p=argparse.ArgumentParser(); p.add_argument('--original',required=True,type=Path); p.add_argument('--directory',required=True,type=Path); p.add_argument('--output',type=Path); a=p.parse_args()
 raw=a.original.read_bytes(); original=json.loads(raw); source=json.loads((a.directory/'source.json').read_text()); cert=json.loads((a.directory/'factor_certificate.json').read_text()); digest=hashlib.sha256(raw).hexdigest()
 metrics=verify(original,source,cert,digest); rejected=[]
 for name in ['row_sign','constructor_sign','hash']:
  s,c=deepcopy(source),deepcopy(cert)
  if name=='row_sign': s['residuals'][-1]['terms'][0][0]*=-1
  elif name=='constructor_sign': s['residuals'][0]['terms'][0][0]*=-1
  else: c['source_sha256']='0'*64
  try: verify(original,s,c,digest)
  except (ValueError,KeyError,TypeError,IndexError): rejected.append(name)
  else: raise ValueError('Mutation accepted: '+name)
 result={'status':'pass','python_optimized':not __debug__,'metrics':metrics,'mutations_rejected':rejected,'original_sha256':digest,
 'refactored_sha256':hashlib.sha256((a.directory/'source.json').read_bytes()).hexdigest(),'proof':'Each added variable is uniquely determined by a monic affine constructor. Exact pullbacks certify both directions over unrestricted integers.'}
 txt=json.dumps(result,sort_keys=True,indent=2)+'\n'
 if a.output: a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_text(txt)
 print(txt,end='')
if __name__=='__main__': main()
