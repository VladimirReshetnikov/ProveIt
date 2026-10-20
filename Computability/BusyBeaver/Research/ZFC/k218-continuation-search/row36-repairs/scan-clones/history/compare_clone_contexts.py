"""Compare exact contexts from retained literal traces, without new candidate runs."""
from pathlib import Path
import gzip,json,hashlib
P=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/candidate-k218')
D=Path('/tmp/k217-row36-marker/clones1')
seed=json.loads((P/'evidence/blank-startup.json').read_text())['final_one_cells']
def contexts(path,wanted):
 trace=json.load(gzip.open(path,'rt'));O=set(seed);q,h=84,-5;got={}
 for n,(aq,ah,b,w,d,z)in enumerate(trace):
  assert (q,h,int(h in O))==(aq,ah,b)
  if(q,b)in wanted and(q,b)not in got:
   got[q,b]={'tick':n,'head':h,'relative_support':sorted(j-h for j in O)}
  O.add(h)if w else O.discard(h);q,h=z,h+d
 return got
xs=[22,25,32,33,48,55,60,64];base=contexts(D/'baseline.trace.json.gz',{(x,0)for x in xs});out=[]
for x in xs:
 new=contexts(D/f'clone{x}.trace.json.gz',{(x,0)})[x,0];old=base[x,0]
 changed=set(old['relative_support'])^set(new['relative_support'])
 nearest=min(map(abs,changed))if changed else None
 out.append({'state':x,'baseline_original_role':old,'clone_q36_role':new,'nearest_different_relative_cells':sorted(p for p in changed if abs(p)==nearest)if changed else [],'identical_window_radius':nearest-1 if nearest is not None else 'whole tape','right_half_equal':{p for p in old['relative_support']if p>=0}=={p for p in new['relative_support']if p>=0}})
(Path('/tmp/k217-row36-marker')/'clone-contexts.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{k:v for k,v in r.items()if k not in('baseline_original_role','clone_q36_role')}for r in out],indent=2))
