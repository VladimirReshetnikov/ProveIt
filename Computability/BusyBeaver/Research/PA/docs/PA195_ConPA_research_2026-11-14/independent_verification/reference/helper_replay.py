#!/usr/bin/env python3
"""Replay the PA196 single arbitrary-helper-row screen and U208 control."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import subprocess
import tempfile
from pathlib import Path
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
SEARCH = HERE
REPO = HERE.parents[6]
U209_MEMBER = 'U208_ConPA_2026-10-29/baseline/u209.native.tm'
U209_SHA = 'd0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16'

def require(condition, message):
    if not condition: raise ValueError(message)

def load_fold():
    spec = importlib.util.spec_from_file_location('pa196_local_folds', SEARCH / 'scan_local_folds.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def contexts_text(contexts):
    lines=[]
    for (q,b), cases in sorted(contexts.items()):
        for tape in cases:
            mask=sum(tape[i]<<(i+2) for i in range(-2,3))
            require(((mask>>2)&1)==b, 'context read bit mismatch')
            lines.append(f'{q} {b} {mask}\n')
    return ''.join(lines)

def table_text(table):
    return ''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n'
                   for (q,b),(w,d,t) in sorted(table.items()))

def run_engine(binary,directory,table,contexts,count,selected=None):
    table_file,context_file,result_file=(directory/x for x in ('table.txt','contexts.txt','results.txt'))
    table_file.write_text(table_text(table),encoding='ascii')
    context_data=contexts_text(contexts)
    context_file.write_text(context_data,encoding='ascii')
    command=[str(binary),str(table_file),str(context_file),str(result_file),str(count)]
    if selected is not None:command += [str(q) for q in selected]
    result=subprocess.run(command,check=True,text=True,capture_output=True)
    words=result.stdout.split()
    require(words[::2]==['pairs','plain','patch_keys','helper_keys','patches','representative_pass','survivors'],
            f'unexpected engine counters: {result.stdout}')
    counts=dict(zip(words[::2],map(int,words[1::2])))
    records=[]
    for line in result_file.read_text().splitlines():
        fields=line.split()
        require(fields[0] in ('rejected','SURVIVOR'), f'unexpected result row: {line}')
        records.append([fields[0],*map(int,fields[1:])])
    require(sum(r[0]=='SURVIVOR' for r in records)==counts['survivors'], 'survivor count mismatch')
    require(len(records)==counts['representative_pass'], 'representative count mismatch')
    return counts,records,hashlib.sha256(context_data.encode('ascii')).hexdigest()

def block(table,count,drop,keep,patch_state,patch_read,row,q,b,mask):
    """Independent Python implementation of a complete local block."""
    project=lambda x: keep if x==drop else x
    write,direction,target=table[q,b]
    goal=(project(target),direction,(mask & ~4)|(write<<2))
    state,head,tape=project(q),0,mask
    seen=set()
    for k in range(16):
        if state>=count:return 'halt-before-match',k
        if not -2<=head<=2:return 'outside-window',k
        triple=(state,head,tape)
        if triple in seen:return 'cycle-before-match',k
        seen.add(triple)
        current=(tape>>(head+2))&1
        w,d,n=row if (state,current)==(patch_state,patch_read) else table[state,current]
        tape=(tape & ~(1<<(head+2)))|(w<<(head+2))
        state,head=project(n),head+d
        if (state,head,tape)==goal:return 'matched',k+1
    return 'step-limit',16

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    fold=load_fold();table,digest=fold.read_table(fold.DEFAULT_TABLE)
    contexts,may_halt,closure_size=fold.blank_window_contexts(table,6)
    require(closure_size==270067 and sum(map(len,contexts.values()))==2774 and may_halt,
            'unexpected PA196 abstraction')
    with ZipFile(REPO/'docs/incoming/U208_ConPA_2026-10-29.zip') as z:data=z.read(U209_MEMBER)
    require(hashlib.sha256(data).hexdigest()==U209_SHA, 'unexpected U209 table hash')
    rows=[line.split() for line in data.decode('ascii').splitlines()
          if line.strip() and not line.startswith('#')]
    labels=sorted({int(row[0]) for row in rows})
    require(len(labels)==209 and {int(row[4]) for row in rows}-set(labels)=={254}, 'unexpected U209 controls')
    dense={q:i for i,q in enumerate(labels)};dense[254]=209
    u209={(dense[int(q)],int(b)):(int(w),1 if d=='R' else -1,dense[int(t)]) for q,b,w,d,t in rows}
    require(len(u209)==418 and dense[0]==0, 'unexpected U209 domain')
    fold.STATES=209;ucontexts,_,_=fold.blank_window_contexts(u209,2)
    udrop,ukeep,uhelper=(dense[q] for q in (211,172,217))
    with tempfile.TemporaryDirectory(prefix='pa196-helper-row-') as d:
        temp=Path(d);binary=temp/'scan'
        subprocess.run(['g++','-O3','-std=c++17','-Wall','-Wextra','-Werror',
                        str(HERE/'scan_helper.cpp'),'-o',str(binary)],check=True)
        counts,records,context_sha=run_engine(binary,temp,table,contexts,196)
        expected={'pairs':38220,'plain':0,'patch_keys':2121,'helper_keys':796,
                  'patches':1662864,'representative_pass':5,'survivors':0}
        require(counts==expected,f'PA196 screen changed: {counts}')
        rejections=[]
        for record in records:
            kind,drop,keep,h,read,w,d,n,q,b,mask=record
            require(kind=='rejected', 'unexpected survivor in stored outcome')
            require(any(sum(tape[i]<<(i+2) for i in range(-2,3))==mask for tape in contexts[q,b]),
                    'witness window is not in closure')
            reason,steps=block(table,196,drop,keep,h,read,(w,d,n),q,b,mask)
            require(reason!='matched',f'C++ rejection matched in Python: {record}')
            rejections.append({'drop':drop,'keep':keep,'patch_state':h,'patch_read':read,
                'patch':[w,'R' if d==1 else 'L',n], 'parent_state':q,'parent_read':b,
                'window_mask':mask,'failure':reason,'steps':steps})
        ccounts,crecords,_=run_engine(binary,temp,u209,ucontexts,209,(udrop,ukeep))
        known=['SURVIVOR',udrop,ukeep,ukeep,0,0,-1,uhelper]
        require(known in crecords, 'known U209 fold was not recovered')
        for orig in {udrop,ukeep}:
            for b in (0,1):
                for tape in ucontexts[orig,b]:
                    mask=sum(tape[i]<<(i+2) for i in range(-2,3))
                    outcome,_=block(u209,209,udrop,ukeep,ukeep,0,(0,-1,uhelper),orig,b,mask)
                    require(outcome=='matched','Python control failed')
        # An independent synthetic four-state table exercises a changed row at
        # a third state: delete 2, keep 0, patch helper 1/read1 to 1 L 3.
        synthetic={(0,0):(1,-1,1), (0,1):(0,-1,3),
                   (1,0):(0,-1,3), (1,1):(1,-1,2),
                   (2,0):(1,-1,1), (2,1):(1,-1,2),
                   (3,0):(0,1,2), (3,1):(1,1,2)}
        synthetic_contexts={(q,b):[] for q in range(4) for b in (0,1)}
        for q in range(4):
            for mask in range(32):
                synthetic_contexts[q,(mask>>2)&1].append({i:(mask>>(i+2))&1 for i in range(-2,3)})
        scounts,srecords,_=run_engine(binary,temp,synthetic,synthetic_contexts,4,(2,0))
        synthetic_known=['SURVIVOR',2,0,1,1,1,-1,3]
        require(synthetic_known in srecords, 'third-state helper control missing')
        for q in (2,0,1):
            for mask in range(32):
                b=(mask>>2)&1
                outcome,_=block(synthetic,4,2,0,1,1,(1,-1,3),q,b,mask)
                require(outcome=='matched','Python third-state helper control failed')
    output={'pa196_table_sha256':digest,'window_invariant_radius':6,
            'closure_windows':closure_size,'projected_contexts':2774,'context_encoding_sha256':context_sha,
            'abstract_halt_reachable':may_halt,'active_window_radius':2,'max_child_steps':16,
            'screen_counts':counts,'representative_pass_rejections':rejections,
            'u209_member_sha256':U209_SHA,'u209_control_counts':ccounts,
            'u209_control_known_fold_recovered':True,
            'u209_control_native_drop_keep_helper':[211,172,217],
            'synthetic_third_state_helper_counts':scounts,
            'synthetic_third_state_helper_fold_recovered':True}
    data=json.dumps(output,indent=2,sort_keys=True)+'\n';print(data,end='')
    if args.output:args.output.write_text(data)

if __name__=='__main__':main()
