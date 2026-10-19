#!/usr/bin/env python3
"""Two-row compiler repair of the new borrowed-tail arithmetic core.
The affine oracle is CONDITIONAL on its matching new arithmetic invariants;
its plain boxes here mean final spare=1, with arbitrary preceding spares.
Rejected bounded symbolic runs are not impossibility results.
"""
from pathlib import Path
import os,sys,json,time,importlib.util,collections
H=Path(__file__).resolve().parent;R=H.parent/'context_folds'
os.environ['ZFC246_BASE']=str(R/'recovered/63');os.environ['ZFC246_TABLE']=str(R/'recovered/63/machine/zfc_prefix246_old.tm')
spec=importlib.util.spec_from_file_location('f',R/'recovered/64/experiments/decoder/fold_search246.py');f=importlib.util.module_from_spec(spec);sys.modules['f']=f;spec.loader.exec_module(f)
base={k:v for k,v in f.T.items() if k[0]!='255'}
base['75',0]=(0,'R','63');base['48',0]=(1,'L','131');base['131',0]=(1,'L','126')
labels=sorted({q for q,b in base},key=int);actions=[(w,d,q) for w in (0,1) for d in ('L','R') for q in labels]
# Exclude all baseline cases using original incoming108/0, not just a chosen sample.
separate=[];affected=[];t0=time.monotonic()
for i in range(len(f.CASES)):
 tr=f.Tracking(f.T);ok,_,_=f.check(tr,i,2000);assert ok
 (affected if ('108',0)in tr.used else separate).append(i)
print('partition',len(separate),len(affected),flush=True)
# CEGIS orders are deterministic. Each survivor gets all separated cases.
witness=separate[:1];candidates=[];stats=collections.Counter();ledger=[]
for action in actions:
 t=base.copy();t['126',0]=action;bad=None
 for i in witness:
  stats['stage1_checks']+=1;ok,_,why=f.check(t,i,2000)
  if not ok:bad=(i,why);break
 if bad is None:
  for i in separate:
   if i in witness:continue
   stats['stage1_checks']+=1;ok,_,why=f.check(t,i,2000)
   if not ok:witness.append(i);bad=(i,why);break
 if bad is None:candidates.append(action);print('126 survivor',action,flush=True)
 else:ledger.append([action,*bad]);stats['reject_'+bad[1]]+=1
 stats['stage1_recipes']+=1
print('stage1',len(candidates),dict(stats),flush=True)
survivors=[];fullwitness=affected[:1]
for a126 in candidates:
 for a108 in actions:
  t=base.copy();t['126',0]=a126;t['108',0]=a108;bad=None
  for i in fullwitness:
   stats['stage2_checks']+=1;ok,_,why=f.check(t,i,2000)
   if not ok:bad=(i,why);break
  if bad is None:
   for i in range(len(f.CASES)):
    if i in fullwitness:continue
    stats['stage2_checks']+=1;ok,_,why=f.check(t,i,2000)
    if not ok:fullwitness.append(i);bad=(i,why);break
  if bad is None:
   hit=dict(row126=a126,row108=a108);survivors.append(hit);print('ALL-8391 AFFINE PASS',hit,flush=True)
   (H/f'borrowed_tail_affine_{len(survivors)}.tm').write_text('#! start 95\n# RESEARCH: macro invariant and startup obligations remain\n'+''.join(f'{q} {b} {w} {d} {s}\n'for(q,b),(w,d,s)in sorted(t.items(),key=lambda x:(int(x[0][0]),x[0][1]))))
  stats['stage2_recipes']+=1
out=dict(status='DONE',family='delete255,75/0=0R63,48/0=1L131,131/0=1L126; arbitrary126/0 and108/0',fuel=2000,spare_interface='Last spare one; preceding spares arbitrary',separated_cases=len(separate),old108_cases=len(affected),stage1_survivors=candidates,survivors=survivors,stats=stats,stage1_witnesses=witness,stage2_witnesses=fullwitness,seconds=time.monotonic()-t0,complete_claim_within_family=not candidates)
# If stage1 survivors exist, changed108 might affect formerly separated cases, hence full rechecks.
# Stage1 exclusion is sound because no changed108 is reached before their first baseline-use divergence;
# a rejected candidate can potentially reach new108, so no exhaustive family theorem is claimed.
out['search_scope_caution']='Stage1 failures may reach modified108 through a new trajectory. Thus pruning can miss a true two-row repair; this is a directed search, not exhaustive over all two-row programs.'
(H/'borrowed_tail_context_search.json').write_text(json.dumps(out,indent=2)+'\n');(H/'borrowed_tail_stage1_ledger.json').write_text(json.dumps(ledger,separators=(',',':'))+'\n');print(json.dumps(out,indent=2),flush=True)
