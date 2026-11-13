#!/usr/bin/env python3
"""Compare selected outside objects and companions with the 90-join inventory."""
from hashlib import sha256
from pathlib import Path
import json
H=Path(__file__).resolve().parent;D=H.parents[1]
SCAN=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'
BASE=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'
OUT=H/'observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(not OUT.exists(),'output exists')
x=json.loads(SCAN.read_text());b=json.loads(BASE.read_text())
need(x['status']=='PASS' and b['status']=='PASS','input status')
old=b['post_headers']['outside'];common=set(x['outside'])&set(old);new=set(x['outside'])-set(old)
need(len(common)==79 and new=={'Mathlib.Tactic.LinearCombination'},'outside set changed')
matched={};count=0
for n in sorted(common):
 selected=x['outside'][n];need(selected['sha256']==old[n]['record']['sha256'],'object mismatch '+n)
 stem=selected['path'][:-6];comps={}
 for suffix,previous in old[n]['companions'].items():
  p=Path(stem+suffix);need(p.is_file()==(previous is not None),'presence mismatch '+n+suffix)
  if previous is not None:
   h=sha(p);need(h==previous['sha256'],'hash mismatch '+n+suffix);count+=1
   comps[suffix]={'path':str(p),'real_path':str(p.resolve(strict=True)),'sha256':h}
  else:comps[suffix]=None
 matched[n]=comps
new_selected=x['outside']['Mathlib.Tactic.LinearCombination'];need(sha(new_selected['path'])==new_selected['sha256'],'new object drift')
result={'status':'PASS','inputs':{str(p):sha(p) for p in (SCAN,BASE)},'matched':matched,'matched_companions':count,
        'new_outside':new_selected,'scope':'current first-selected outside files and companion hashes versus prior 90-join inventory; no outside-transitive/dynamic/historical source provenance'}
OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','common':len(common),'new':len(new),'matched_companions':count,'sha256':sha(OUT)},sort_keys=True))
