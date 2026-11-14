#!/usr/bin/env python3
"""Replay exact20representative census and nine archived output bijections."""
if not __debug__:
    raise RuntimeError("Verification requires Python without -O or -OO.")

from pathlib import Path
from collections import Counter
import json,hashlib
from canonical import canonical,source_graph
HERE=Path(__file__).resolve().parent

def main():
 m=json.loads((HERE/'manifest.json').read_text());computed={};u208=[]
 for r in m['representatives']:
  d=canonical(HERE/r['path'])
  for key in('working_states','rows','halt','sha256','canonical_sha256'):assert d[key]==r[key],(r['name'],key)
  computed[r['name']]=d
  if d['working_states']==208:u208.append(d)
 assert len(u208)==20
 # Equality/inequality of the full canonical tables is decisive, not the hash.
 assert len({tuple(map(tuple,d['canonical_rows']))for d in u208})==20
 aliases=[]
 for r in m['principal_output_aliases']:
  base=computed[r['base_representative']]
  forward={int(q):int(k)for q,k in r['original_to_canonical_labels'].items()}
  inverse={k:q for q,k in forward.items()}
  assert len(inverse)==209 and inverse[0]==0 and inverse[-1]==208
  rows=sorted([inverse[q],b,w,d,inverse[n]]for q,b,w,d,n in base['canonical_rows'])
  text=r['header']+''.join(f'{q} {b} {w} {d} {n}\n'for q,b,w,d,n in rows)
  assert hashlib.sha256(text.encode()).hexdigest()==r['original_sha256'],r['name']
  aliases.append({'name':r['name'],'graph_class':r['graph_class'],'exact_original_bytes_reconstructed':True})
 assert len(aliases)==9 and len({a['graph_class']for a in aliases})==2
 sources={}
 for k,r in m['u208_source_maps'].items():
  path=HERE/r['path'];assert hashlib.sha256(path.read_bytes()).hexdigest()==r['sha256']
  sources[k]=source_graph(path)
 a,ag=sources['A'];b,bg=sources['B']
 assert [s[1:]for s in a]==[s[1:]for s in b]and ag==bg
 assert len(a)==3909
 source={'sites':len(a),'primitive_word_equal':True,'ordinal_control_graph_equal':True,'different_addresses':sum(x[0]!=y[0]for x,y in zip(a,b)),
 'max_address_depths':[max(len(s[0])for s in ss)for ss in(a,b)],'opcode_counts':dict(Counter(s[1]for s in a))}
 assert source['different_addresses']==720 and source['max_address_depths']==[42,41]
 result={'result':'PASS','accepted_u208_representatives':20,'distinct_rooted_action_labelled_graphs':20,'principal_output_count':9,'principal_output_graph_classes':2,
 'principal_outputs':aliases,'u208_source_comparison':source,'requested_jamesyc_machines':{n:{k:computed[n][k]for k in('working_states','rows','halt','sha256')}for n in('pa196.tm','pa209.tm')},
 'scope':'Exact table, state-count, graph-isomorphism, and source-control-flow claims only. No local-helper equivalence proof or PA/kernel theorem is established by this checker.'}
 (HERE/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
