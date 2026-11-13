#!/usr/bin/env python3
"""Search an arbitrary changed helper row against alternative196 radius-six contexts."""
from pathlib import Path
from zipfile import ZipFile
import argparse,hashlib,importlib.util,json,subprocess,tempfile
HERE=Path(__file__).resolve().parent;ALT=HERE.parent;SEARCH=HERE.parents[2]/'search';HELPER=SEARCH/'helper-row';REPO=HERE.parents[7]
EXPECTED='aa05f079326ae244c725d611fd50f8ed1e4e9519907e28788dbb2172deee1b95'
U209='d0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16'
def need(x,msg):
 if not x:raise ValueError(msg)
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--candidate-dir',type=Path);args=p.parse_args()
subprocess.run(['python3','-B',str(ALT/'check_archive.py')],check=True,capture_output=True)
fold=load('alt196_folds',SEARCH/'scan_local_folds.py');support=load('pa196_helper',HELPER/'replay.py');fold.EXPECTED_HASH=EXPECTED
table,digest=fold.read_table(ALT/'alternative196.tm');classes,seen=fold.partition_and_reachability(table)
contexts,may_halt,closure=fold.blank_window_contexts(table,6)
with ZipFile(REPO/'docs/incoming/U208_ConPA_2026-10-29.zip') as z:data=z.read('U208_ConPA_2026-10-29/baseline/u209.native.tm')
need(hashlib.sha256(data).hexdigest()==U209,'U209 control hash')
rows=[line.split() for line in data.decode().splitlines() if line.strip() and not line.startswith('#')];labels=sorted({int(row[0])for row in rows});need(len(labels)==209,'U209 census');dense={q:i for i,q in enumerate(labels)};dense[254]=209
u209={(dense[int(q)],int(b)):(int(w),1 if d=='R' else -1,dense[int(t)])for q,b,w,d,t in rows}
fold.STATES=209;ucontexts,_,_=fold.blank_window_contexts(u209,2);udrop,ukeep,uhelper=(dense[q] for q in (211,172,217))
with tempfile.TemporaryDirectory(prefix='alt196-helper-') as directory:
 tmp=Path(directory);binary=tmp/'scan';closure_binary=tmp/'closure'
 subprocess.run(['g++','-O3','-std=c++17','-Wall','-Wextra','-Werror',str(HELPER/'window_closure.cpp'),'-o',str(closure_binary)],check=True)
 closure_run=subprocess.run([str(closure_binary),str(ALT/'alternative196.tm'),'6'],check=True,capture_output=True,text=True)
 fields=closure_run.stdout.split();need(fields[:8]==['radius','6','closure',str(closure),'projected',str(sum(map(len,contexts.values()))),'may_halt',str(int(may_halt))],'independent C++ closure census mismatch')
 subprocess.run(['g++','-O3','-std=c++17','-Wall','-Wextra','-Werror',str(HELPER/'scan_helper.cpp'),'-o',str(binary)],check=True)
 counts,records,context_sha=support.run_engine(binary,tmp,table,contexts,196)
 rejections=[];survivors=[]
 for record in records:
  kind,drop,keep,h,read,w,d,n,q,b,mask=record
  if kind=='rejected':
   need(any(sum(tape[i]<<(i+2) for i in range(-2,3))==mask for tape in contexts[q,b]),'rejection not in closure')
   reason,steps=support.block(table,196,drop,keep,h,read,(w,d,n),q,b,mask);need(reason!='matched','C++ rejection matched in Python')
   rejections.append({'drop':drop,'keep':keep,'patch_state':h,'patch_read':read,'patch':[w,'R' if d==1 else 'L',n],'parent_state':q,'parent_read':b,'window_mask':mask,'failure':reason,'steps':steps})
  else:
   for orig in {drop,keep,h}:
    for bit in (0,1):
     for tape in contexts[orig,bit]:
      local=sum(tape[i]<<(i+2) for i in range(-2,3));outcome,_=support.block(table,196,drop,keep,h,read,(w,d,n),orig,bit,local)
      need(outcome=='matched','survivor failed independent full affected-state checks')
   survivors.append({'drop':drop,'keep':keep,'patch_state':h,'patch_read':read,'patch':[w,'R' if d==1 else 'L',n]})
   if args.candidate_dir is not None:
    args.candidate_dir.mkdir(parents=True,exist_ok=True);candidate={(state,bit):(w0,d0,keep if target==drop else target)for (state,bit),(w0,d0,target)in table.items()if state!=drop};candidate[h,read]=(w,d,keep if n==drop else n)
    text='#! start '+str(keep if drop==0 else 0)+'\n'+support.table_text(candidate);(args.candidate_dir/('candidate-'+str(len(survivors))+'.native.tm')).write_text(text)
 ccounts,crecords,_=support.run_engine(binary,tmp,u209,ucontexts,209,(udrop,ukeep));need(['SURVIVOR',udrop,ukeep,ukeep,0,0,-1,uhelper] in crecords,'U209 known fold missing')
 for orig in {udrop,ukeep}:
  for b in (0,1):
   for tape in ucontexts[orig,b]:
    mask=sum(tape[i]<<(i+2)for i in range(-2,3));need(support.block(u209,209,udrop,ukeep,ukeep,0,(0,-1,uhelper),orig,b,mask)[0]=='matched','Python U209 control')
 synthetic={(0,0):(1,-1,1),(0,1):(0,-1,3),(1,0):(0,-1,3),(1,1):(1,-1,2),(2,0):(1,-1,1),(2,1):(1,-1,2),(3,0):(0,1,2),(3,1):(1,1,2)}
 sc={(q,b):[]for q in range(4)for b in (0,1)}
 for q in range(4):
  for mask in range(32):sc[q,(mask>>2)&1].append({i:(mask>>(i+2))&1 for i in range(-2,3)})
 scounts,srecords,_=support.run_engine(binary,tmp,synthetic,sc,4,(2,0));need(['SURVIVOR',2,0,1,1,1,-1,3] in srecords,'helper control missing')
 for q in (2,0,1):
  for mask in range(32):need(support.block(synthetic,4,2,0,1,1,(1,-1,3),q,(mask>>2)&1,mask)[0]=='matched','Python helper control')
result={'alternative_literal_sha256':digest,'independent_cpp_closure_census_matches':True,'window_invariant_radius':6,'closure_windows':closure,'projected_contexts':sum(map(len,contexts.values())),'context_encoding_sha256':context_sha,'abstract_halt_reachable':may_halt,'working_states_reachable':len(seen),'bisimulation_classes':classes,'active_window_radius':2,'max_child_steps':16,'screen_counts':counts,'representative_pass_rejections':rejections,'survivors_independently_checked_on_all_affected_states':survivors,'u209_member_sha256':U209,'u209_control_counts':ccounts,'u209_control_native_drop_keep_helper':[211,172,217],'synthetic_third_state_helper_counts':scounts,'scope':'Only one deleted state, direct state projection, one patched row, and <=16 child steps per original step within a five-cell window.'}
args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2,sort_keys=True))
