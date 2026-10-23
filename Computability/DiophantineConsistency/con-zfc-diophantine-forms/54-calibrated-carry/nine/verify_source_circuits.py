#!/usr/bin/env python3
"""Independent exact Dcode verification for all retained nine circuits."""
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'source'))
from verify_selective_source import add,mul,expr,need

def main():
 reports=[]
 for path in sorted((ROOT/'generated').glob('nine_*.json')):
  obj=json.loads(path.read_text());certpath=ROOT.parent/obj['positional_certificate'];cert=json.loads(certpath.read_text())
  need(hashlib.sha256(certpath.read_bytes()).hexdigest()==obj['positional_certificate_sha256'],'Certificate hash')
  portenv={p:{tuple(int(i+1==j)for j in range(5)):1}for i,p in enumerate(['beta','K0','MC','MF'])}
  expected={}
  for row in cert['rows']:
   for term in row['terms']:
    coeff=expr(term['weighted_coefficient'],portenv,5)
    expected=add(expected,{(m[0]+term['encoding_exponent'],)+m[1:]:c for m,c in coeff.items()})
  fixed={rec['name']:{(0,)+tuple(t['powers']):t['coefficient']for t in rec['terms']}for rec in obj['coefficient_recipes']}
  nodes=obj['nodes'];base=obj['named_nodes']['B'];out=obj['named_nodes']['Dcode'];anc=set();todo=[out]
  while todo:
   ix=todo.pop()
   if ix in anc:continue
   anc.add(ix)
   if ix==base:continue
   node=nodes[ix]
   if'left'in node:todo.extend([node['left'],node['right']])
  vals={}
  for ix in sorted(anc):
   node=nodes[ix];kind=node['kind']
   if ix==base:p={(1,0,0,0,0):1}
   elif kind=='literal':p={(0,)*5:node['value']}if node['value']else{}
   elif kind=='fixed':p=fixed[node['name']]
   elif kind in('add','sub','mul'):p=mul(vals[node['left']],vals[node['right']])if kind=='mul'else add(vals[node['left']],vals[node['right']],1 if kind=='add'else -1)
   else:raise ValueError(('Unexpected source ancestor',ix,node))
   vals[ix]=p
  need(vals[out]==expected,'Exact source polynomial mismatch: '+path.name)
  # Independently verify the target polynomial, including the logarithmic
  # geometric-sum circuit used for regular target progressions.
  target=obj['named_nodes']['targets'];ta=set();todo=[target]
  while todo:
   ix=todo.pop()
   if ix in ta:continue
   ta.add(ix)
   if ix==base:continue
   node=nodes[ix]
   if 'left'in node:todo.extend([node['left'],node['right']])
  tv={}
  for ix in sorted(ta):
   node=nodes[ix];kind=node['kind']
   if ix==base:p={(1,0,0,0,0):1}
   elif kind=='literal':p={(0,)*5:node['value']}if node['value']else{}
   elif kind in('add','sub','mul'):p=mul(tv[node['left']],tv[node['right']])if kind=='mul'else add(tv[node['left']],tv[node['right']],1 if kind=='add'else -1)
   else:raise ValueError(('Unexpected target ancestor',ix,node))
   tv[ix]=p
  target_expected={(row['target_exponent'],0,0,0,0):1 for row in cert['rows']}
  need(tv[target]==target_expected,'Exact target-mask polynomial mismatch: '+path.name)
  reports.append(dict(file=path.name,encoding=obj['encoding'],target_terms_verified=len(target_expected),target_ancestor_nodes=len(ta),exact_symbolic_terms=len(expected),source_ancestor_nodes=len(anc),sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
 out=dict(status='PASS',method='Exact Dcode and targetsum equality in Z[B,beta,K0,MC,MF], cutting the base B and no numerical specialization',circuits=len(reports),results=reports)
 (ROOT/'SOURCE_CIRCUIT_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='results'},indent=2))
if __name__=='__main__':main()
