#!/usr/bin/env python3
"""Earlier-marker variants of borrowed-tail core. Bounded affine screen only."""
from pathlib import Path
import sys,json,os,time,importlib.util,collections,itertools
H=Path(__file__).resolve().parent;R=H.parent/'context_folds';os.environ['ZFC246_BASE']=str(R/'recovered/63');os.environ['ZFC246_TABLE']=str(R/'recovered/63/machine/zfc_prefix246_old.tm')
spec=importlib.util.spec_from_file_location('f',R/'recovered/64/experiments/decoder/fold_search246.py');f=importlib.util.module_from_spec(spec);sys.modules['f']=f;spec.loader.exec_module(f)
base={k:v for k,v in f.T.items()if k[0]!='255'};base['75',0]=(0,'R','63');base['48',0]=(1,'L','131');base['131',0]=(1,'L','126')
labels=sorted({q for q,b in base},key=int);actions=list(itertools.product((0,1),('L','R'),labels));reports=[];start=time.monotonic()
for incbit,decbit in [(1,0),(0,1),(1,1)]:
 t0=time.monotonic();b=base.copy();b['57',1]=(incbit,'R','73');b['30',1]=(decbit,'R','95');stats=collections.Counter();unresolved=[];proof=[];witnesses=[0,1]
 for a126 in actions:
  t=f.Tracking(b|{('126',0):a126});bad=None
  # A rejection before any108/0 read cannot be altered by an108/0 repair.
  for i in witnesses:
   t.used.clear();ok,_,why=f.check(t,i,2000);stats['stage1_checks']+=1
   if not ok:bad=(i,why,('108',0)in t.used);break
  if bad is None:
   for i in range(len(f.CASES)):
    if i in witnesses:continue
    t.used.clear();ok,_,why=f.check(t,i,2000);stats['stage1_checks']+=1
    if not ok:bad=(i,why,('108',0)in t.used);witnesses.append(i);break
  if bad is None or bad[2]:unresolved.append(a126)
  else:proof.append([a126,*bad]);stats['safely_pruned']+=1
 print('marker',incbit,decbit,'unresolved',len(unresolved),'stats',dict(stats),flush=True)
 survivors=[];witness2=[0,1]
 for a126 in unresolved:
  for a108 in actions:
   t=b|{('126',0):a126,('108',0):a108};bad=None
   for i in witness2:
    ok,_,why=f.check(t,i,2000);stats['stage2_checks']+=1
    if not ok:bad=(i,why);break
   if bad is None:
    for i in range(len(f.CASES)):
     if i in witness2:continue
     ok,_,why=f.check(t,i,2000);stats['stage2_checks']+=1
     if not ok:bad=(i,why);witness2.append(i);break
   if bad is None:
    hit=dict(marker=[incbit,decbit],row126=a126,row108=a108);survivors.append(hit);print('SURVIVOR',hit,flush=True)
    (H/f'borrowed_marker_{incbit}{decbit}_{len(survivors)}.tm').write_text('#! start95\n# Research candidate; new macro invariant and bootstrap require proof\n'+''.join(f'{q} {v} {w} {d} {s}\n'for(q,v),(w,d,s)in sorted(t.items(),key=lambda x:(int(x[0][0]),x[0][1]))))
   stats['stage2_recipes']+=1
 report=dict(marker=[incbit,decbit],stats=stats,unresolved126=unresolved,survivors=survivors,stage1_witnesses=witnesses,stage2_witnesses=witness2,seconds=time.monotonic()-t0,exhaustive_with_safe_pruning=True,fuel=2000)
 reports.append(report);(H/'borrowed_marker_search.json').write_text(json.dumps(dict(status='DONE'if len(reports)==3 else'RUNNING',reports=reports,seconds=time.monotonic()-start),indent=2)+'\n');(H/f'borrowed_marker_pruning_{incbit}{decbit}.json').write_text(json.dumps(proof,separators=(',',':'))+'\n');print('DONE MARKER',incbit,decbit,'survivors',len(survivors),'seconds',time.monotonic()-t0,flush=True)
