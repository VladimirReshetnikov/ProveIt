#!/usr/bin/env python3
"""Reconstruct 936 jump-action products; optionally replay the scoped fold search.

Default mode is a fast all-natural instruction-contract check. --folds needs
g++ and additionally replays the radius6 / five-cell / sixteen-step search.
No sub-196 machine or state lower bound is asserted.
"""
from pathlib import Path
from itertools import product
from collections import defaultdict
import argparse,json,sys,subprocess,time,tempfile

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'zero_jump_machine'))
import verify as V
S=V.S
import scan_local_folds as L

GROUPS=[
 {'native':27,'sites':[26],'zero':[3,6,7]},
 {'native':103,'sites':[3,9,3665,3671,3683,3689,3766,3772],'zero':[3,6]},
 {'native':1365,'sites':[3692],'zero':[3,4,5,6,7]},
]
ZEROS={i:frozenset(S.PHYSICAL[r]for r in g['zero'])for g in GROUPS for i in g['sites']}

def run(table,c,trace=None):
 i,kind,branch,start,target=c
 return S.execute(table,ZEROS.get(i,branch),start,target,fuel=1024,record=trace)

def write_table(table,path):
 path.write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {t}\n'
                       for(q,b),(w,d,t)in sorted(table.items())))

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--folds',action='store_true')
 p.add_argument('--output',type=Path,default=HERE/'reproduced_products.json')
 a=p.parse_args();started=time.monotonic()
 V.check_inputs();sites=S.all_sites();inv=V.reconstruct_invariant(sites)
 certified={x['site']:set(x['zero_registers'])for x in inv['eligible_forward_jumps']}
 for g in GROUPS:
  V.require(all(set(g['zero'])<=certified[i]for i in g['sites']),'zero precondition')
 baseline=S.load_machine();contracts=S.contracts()
 affected=defaultdict(list)
 for n,c in enumerate(contracts):
  trace=[];V.require(run(baseline,c,trace)is not None,('baseline',c[:2]))
  for key in {k for kind,conf,k in trace if kind!='oracle'}:affected[key].append(n)
 keys=[(S.LITERAL[g['native']],1)for g in GROUPS]
 choices=[]
 for g,key in zip(GROUPS,keys):
  valid=[];table=dict(baseline)
  ids=sorted(affected[key],key=lambda n:(contracts[n][0]not in g['sites'],n))
  for target in range(197):
   for write in(0,1):
    for move in(-1,1):
     table[key]=(write,move,target)
     if all(run(table,contracts[n])is not None for n in ids):valid.append([write,move,target])
  choices.append(valid)
 V.require(list(map(len,choices))==[12,6,13],'recognized action counts changed')
 ids=sorted(set(n for key in keys for n in affected[key]))
 expected=json.loads((HERE/'recorded_products.json').read_text())
 expected_by_id={r['index']:r for r in expected['records']}
 records=[];rejected=0;folds=[]
 with tempfile.TemporaryDirectory(prefix='pa-jump-products-') as temporary:
  tmp=Path(temporary);exe=tmp/'focused_helper'
  if a.folds:
   subprocess.run(['g++','-O3','-std=c++17',str(HERE/'focused_helper.cpp'),'-o',str(exe)],check=True)
  for index,actions in enumerate(product(*choices)):
   table=dict(baseline)
   for key,action in zip(keys,actions):table[key]=tuple(action)
   if table==baseline:continue
   V.require(S.check_engine(table),'engine rows changed')
   fail=next((list(contracts[n][:2])for n in ids if run(table,contracts[n])is None),None)
   old=expected_by_id[index]
   V.require(old['actions']==list(actions),'product order differs')
   V.require((fail is None)==(old['status']=='runtime_pass'),'product classification differs')
   record=dict(index=index,actions=actions,runtime_failure=fail)
   if fail is not None:rejected+=1
   elif a.folds:
    tablepath=tmp/'parent.tm';contextpath=tmp/'contexts.txt';matchpath=tmp/'matches.txt'
    write_table(table,tablepath)
    contexts,mayhalt,size=L.blank_window_contexts(table,6)
    contextpath.write_text(''.join(f'{q} {b} {sum(t[i]<<(i+2)for i in range(-2,3))}\n'
                         for(q,b),ts in sorted(contexts.items())for t in ts))
    focus={k[0]for k in keys if table[k]!=baseline[k]}
    process=subprocess.run([str(exe),str(tablepath),str(contextpath),str(matchpath),'196',
                            ','.join(map(str,sorted(focus)))],capture_output=True,text=True,check=True)
    matches=[x for x in matchpath.read_text().splitlines()if x.startswith(('SURVIVOR','PLAIN'))]
    V.require(matches==old['folds'],'fold result differs')
    V.require(size==old['closure_windows'],'window closure differs')
    record.update(closure_windows=size,folds=matches,counts=process.stdout.strip())
    folds.extend(matches)
   records.append(record)
   if index%100==0:print('checked',index,'of936',flush=True)
 V.require(len(records)==935 and rejected==264,'final product counts changed')
 if a.folds:V.require(not folds,'unexpected surviving fold')
 out=dict(status='PASS',sub196_machine_certified=False,action_counts=list(map(len,choices)),
          modified_combinations=len(records),runtime_pass=671,runtime_reject=264,
          fold_search_replayed=a.folds,fold_survivors=folds if a.folds else None,
          seconds=time.monotonic()-started,records=records,
          scope='Default: all affected symbolic instruction contracts plus finite invariant; --folds: exact recorded five-cell/sixteen-step one-helper-row search, not an unrestricted state lower bound.')
 a.output.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items()if k!='records'},indent=2))

if __name__=='__main__':main()
