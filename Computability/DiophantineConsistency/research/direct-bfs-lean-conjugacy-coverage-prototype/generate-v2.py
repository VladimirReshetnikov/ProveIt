#!/usr/bin/env python3
"""Create immutable 16-entry Lean proof chunks with exact range coverage."""
from pathlib import Path
from hashlib import sha256
import json,sys
H=Path(__file__).resolve().parent
out=H/'chunks-v2'; manifest=H/'coverage-manifest-v2.json'
if out.exists() or manifest.exists():raise SystemExit('refusing existing generated targets')
out.mkdir()
records=[]
for i,start in enumerate(range(0,943,16)):
 name=f'DirectBFSCoverage{i:03d}'
 rows=min(16,943-start)
 groups=[('rows', 'checkRows',rows),('inverse','checkRowInverse',rows)]
 if start<250:groups.append(('horizontal','checkHorizontal',min(16,250-start)))
 if start<439:groups.append(('vertical','checkVertical',min(16,439-start)))
 src='import DirectBFSConjugacyChunk\nset_option autoImplicit false\nset_option Elab.async false\nset_option maxRecDepth 16384\nset_option maxHeartbeats 30000000\nnamespace DirectBFSCoverage\nopen DirectBFSConjugacyChunk\n'
 for label,check,n in groups:
  src+=f'theorem {label}_{i:03d} : {check} {start} {n}=true := by decide\n'
  if label != 'rows':
   forward,inverse,limit={'inverse':('rowMap','rowInverse',943),'horizontal':('horizontal','horizontalInverse',250),'vertical':('vertical','verticalInverse',439)}[label]
   src+=f'theorem {label}bounds_{i:03d} : (List.range\' {start} {n}).all (fun j => decide (DirectBFSConjugacyBase.{forward}.getD j 0 < {limit} ∧ DirectBFSConjugacyBase.{inverse}.getD j 0 < {limit})) = true := by decide\n'
 for label,check,n in groups:
  src+=f'#print axioms DirectBFSCoverage.{label}_{i:03d}\n'
  if label != 'rows':src+=f'#print axioms DirectBFSCoverage.{label}bounds_{i:03d}\n'
 src+='end DirectBFSCoverage\n'
 p=out/(name+'.lean');p.write_text(src)
 records.append({'index':i,'module':name,'source_sha256':sha256(p.read_bytes()).hexdigest(),'ranges':[{'kind':x,'start':start,'count':n} for x,_,n in groups]+[{'kind':x+'bounds','start':start,'count':n} for x,_,n in groups if x!='rows']})
for kind,end in [('rows',943),('inverse',943),('horizontal',250),('vertical',439),('inversebounds',943),('horizontalbounds',250),('verticalbounds',439)]:
 coverage=[j for r in records for x in r['ranges'] if x['kind']==kind for j in range(x['start'],x['start']+x['count'])]
 if coverage!=list(range(end)):raise ValueError('bad coverage '+kind)
manifest.write_text(json.dumps({'chunk_size':16,'records':records,'claim':'index coverage of finite checks only'},indent=2,sort_keys=True)+'\n')
print(f'generated {len(records)} chunks with exact disjoint coverage')
