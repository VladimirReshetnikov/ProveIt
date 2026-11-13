#!/usr/bin/env python3
"""Read-only check of seven staged 80 helper producer receipts."""
from hashlib import sha256
from pathlib import Path
import json

H=Path(__file__).resolve().parent
D=H.parents[1]
R=D/'research'
SCAN=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'
OUT=H/'observations/attempt01.json'
cases={
 'Direct80ProjectionProduct':'ten-positive-80-projection-product-prototype/observations/product-attempt03',
 'Direct80UnweightedProjection':'ten-positive-80-projection-product-prototype/observations/unweighted-attempt01',
 'Direct80ProductPower':'ten-positive-80-projection-product-prototype/observations/power-attempt02',
 'Direct80Coprime':'ten-positive-80-rank-parity-prototype/observations/coprime-attempt02',
 'Direct80Parity':'ten-positive-80-rank-parity-prototype/observations/parity-attempt01',
 'Direct80FixedBetaOdd':'ten-positive-80-rank-parity-prototype/observations/betaodd-attempt02',
 'Direct80IndexOne':'ten-positive-80-scaled-growth-prototype/observations/indexone-attempt02',
}
def sha(p): return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b: raise RuntimeError(m)
need(not OUT.exists(),'output exists')
x=json.loads(SCAN.read_text()); need(x['status']=='PASS','closure failed')
out={}
for name,rel in cases.items():
 directory=R/rel; f=directory/'result.json'; record=json.loads(f.read_text())
 need(record['status']=='PASS','producer failed '+name)
 stage=next(s for s in record['stages'] if s['module']==name)
 need(stage['exit']==0 and stage['reason'] is None,'stage failed '+name)
 chosen=x['project'][name]['selected']
 need(sha(chosen['path'])==chosen['sha256']==stage['object_sha256'],'object mismatch '+name)
 source=directory/'stage-01.source.lean'
 need(sha(source)==stage['source_sha256']==record['sources'][name],'source snapshot mismatch '+name)
 need(sha(directory/'stage-01.stdout')==stage['stdout_sha256'],'stdout mismatch '+name)
 need(sha(directory/'stage-01.stderr')==stage['stderr_sha256'],'stderr mismatch '+name)
 for p,h in record['predecessors'].items(): need(sha(p)==h,'pinned predecessor mismatch '+name)
 roots=[Path(p) for p in record['lean_path'].split(':')]
 roots.append(Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'))
 deps={}
 for dep in set(x['fresh_headers'][name]):
  relp=dep.replace('.','/')+'.olean'
  choices=[r/relp for r in roots if (r/relp).is_file()]
  need(choices,'producer path unresolved '+name+' '+dep)
  final=x['project'].get(dep,{}).get('selected',x['outside'].get(dep))
  need(final is not None and sha(choices[0])==final['sha256'],'producer/final dependency differs '+name+' '+dep)
  deps[dep]={'producer_path':str(choices[0]),'sha256':sha(choices[0])}
 out[name]={'receipt':str(f),'receipt_sha256':sha(f),'source':str(source),'source_sha256':sha(source),
            'object':chosen,'dependencies_now':deps,'explicit_predecessors':record['predecessors']}
result={'status':'PASS','closure_sha256':sha(SCAN),'cases':out,
        'scope':'matching staged source/object snapshots, explicitly pinned predecessors, and current re-resolution; not full producer-time transitive provenance'}
OUT.parent.mkdir(parents=True,exist_ok=True)
OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','cases':len(out),'result_sha256':sha(OUT)},sort_keys=True))
