import sys,json,itertools,time,collections
from pathlib import Path
W=Path(__file__).parent;sys.path.insert(0,str(W/'base'))
import compiler as c
import build194 as bld
R=bld.read_table(W/'base/unfolded201.native.tm')
folds=json.loads((W/'base/pa194.folds.json').read_text())
rotations=[r for r in json.loads((W/'fixed_rotation_results.json').read_text())if r.get('source_equal')and r.get('old_folds_valid')]
for rec in rotations:
 q,r,di=rec['q'],rec['r'],rec['direction'];a0,a1=R[q,0],R[q,1];r0,r1=R[r,0],R[r,1]
 if di==1:rec['patch']={(q,0):(0,True,r),(q,1):(1,True,r1[2]),(r,0):(0,True,a0[2]),(r,1):(1,True,r0[2])}
 else:rec['patch']={(q,0):(0,True,r0[2]),(q,1):(1,True,r),(r,0):(0,True,r1[2]),(r,1):(1,True,a1[2])}
n=0;hits=[];t=time.monotonic()
for mask in range(1,1<<len(rotations)):
 subset=[rec for i,rec in enumerate(rotations)if mask>>i&1]
 qs=[q for rec in subset for q in(rec['q'],rec['r'])]
 if len(set(qs))<len(qs):continue
 n+=1;RR=dict(R)
 for rec in subset:RR.update(rec['patch'])
 folded,aliases=bld.apply_folds(RR,folds)
 # fully generic all-state pure-reader history fold candidates
 sh={z:None for z,bit in folded if z not in c.BOXSTATES and z!=84}
 opts=c.opportunities_fast(folded,sh)
 if not opts:continue
 try:bld.check_local_folds(RR,folded,aliases,folds)
 except Exception:continue
 incoming=collections.defaultdict(set)
 for(s,b),(w,d,z)in folded.items():incoming[z].add((w,d))
 for aa,bb,acts in opts:
  if incoming[aa]!={(0,True)}or incoming[bb]!={(1,True)}:continue
  for ac in itertools.product(*acts):
   f=[(aa,bb,ac)];out,al=bld.apply_folds(folded,f)
   try:local=bld.check_local_folds(folded,out,al,f)
   except Exception:continue
   hit={'mask':mask,'rotations':[{k:v for k,v in rec.items()if k!='patch'}for rec in subset],'pair':[aa,bb],'acts':ac};hits.append(hit);print('HIT',json.dumps(hit),flush=True)
   folder=W/f'combined193_{mask}_{aa}_{bb}';folder.mkdir(exist_ok=True)
   (folder/'machine.native.tm').write_text(bld.table_text(out));(folder/'receipt.json').write_text(json.dumps(hit,indent=2));(folder/'local.json').write_text(json.dumps(local))
 print('PROGRESS',n,mask,len(hits),time.monotonic()-t,flush=True)if n%200==0 else None
summary={'rotation_candidates':len(rotations),'compatible_subsets_checked':n,'hits':hits,'elapsed':time.monotonic()-t}
(W/'fixed_combination_results.json').write_text(json.dumps(summary,indent=2));print(summary,flush=True)
