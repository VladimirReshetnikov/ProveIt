#!/usr/bin/env python3
from pathlib import Path
import os,sys,json,importlib.util,collections,time
H=Path(__file__).resolve().parent;R=H.parent/'context_folds';os.environ['ZFC246_BASE']=str(R/'recovered/63');os.environ['ZFC246_TABLE']=str(R/'recovered/63/machine/zfc_prefix246_old.tm')
spec=importlib.util.spec_from_file_location('f',R/'recovered/64/experiments/decoder/fold_search246.py');f=importlib.util.module_from_spec(spec);sys.modules['f']=f;spec.loader.exec_module(f)
base={k:v for k,v in f.T.items() if k[0]!='255'};base['75',0]=(0,'R','63');base['48',0]=(1,'L','131');base['131',0]=(1,'L','126')
ledger=json.loads((H/'borrowed_tail_stage1_ledger.json').read_text());counts=collections.Counter();unresolved=[];reports=[]
for action,case,reason in ledger:
 t=f.Tracking(base|{('126',0):tuple(action)});ok,_,why=f.check(t,case,2000);assert not ok
 reached=('108',0)in t.used;counts['may_depend_on_108'if reached else'certified_no108_failure']+=1
 if reached:unresolved.append(action)
 reports.append([action,case,why,reached])
out=dict(status='DONE',pruned=len(ledger),counts=counts,unresolved126_actions=unresolved,conclusion='No modified108 transition is read on any rejecting prefix, so changing108/0 cannot rescue these980 rows.'if not unresolved else'Directed pruning incomplete; unresolved candidates require108 search.',scope='Affine checker obstruction, including unsupported/fuel; not an impossibility theorem for arbitrary macros.')
(H/'borrowed_tail_pruning_audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
