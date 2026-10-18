#!/usr/bin/env python3
"""Bounded source/audit check of the independent exact246 fast transition tree.

Reuses only exact successful TablePrefix246 and its Core ancestor. No version
query, dependency rebuild or download. Serial -j1 -M4096, default proof limits,
shared 120-second source/audit bound. --prepare-only executes no proof command.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
SOURCE_SHA='dec5303498f4ae17469e8ef79d684f3aaffd959e37a10880261cc200f602e031'
AUDIT_SHA='15cc1876e299dab7b381a188563fb2aa45733455f74a4c76bf7bba513a3418e2'
PARENT_SHA='70a9a9bfb1546a1c0c6f1503c6261d2d23637dd901e7debec220e7185137ed6d'
PROBES=['SetTheory.BusyBeaver.ZFC.FastTablePrefix246.'+n for n in ['fast_transition_eq','fastMachine_eq']]
MODULE='BusyBeaver.ZFC.FastTablePrefix246'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(c,m):
    if not c:raise RuntimeError(m)
def imports(p):return re.findall(r'^import\s+(\S+)\s*$',p.read_text(),re.M)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=REPO)
    ap.add_argument('--source',type=Path,default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/FastTablePrefix246.lean')
    ap.add_argument('--audit',type=Path,default=HERE/'fast_table_prefix246_audit.lean')
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--prepare-only',action='store_true')
    a=ap.parse_args();repo=a.repo.resolve();S=a.source.resolve();A=a.audit.resolve();W=a.output.resolve()
    need(not W.is_relative_to(repo) and (not W.exists() or not any(W.iterdir())),'Use new/empty external output.')
    need(sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA,'Source or audit changed.')
    P=repo/'Computability/BusyBeaver/Research/ZFC/results/table-prefix246-verification.json'
    need(sha(P)==PARENT_SHA,'Selected table parent changed.')
    parent=json.loads(P.read_text());need(parent['status']=='PASS' and parent['named_axiom_probes']==47 and
        parent['callers']==47 and parent['only_standard_axioms'] and parent['all_input_provider_postchecks'] and
        parent['all_fresh_objects_unchanged_after_audit'],'Incomplete successful table parent.')
    need([r['label'] for r in parent['commands']]==['source','audit'] and
        all(r['exit_code']==0 for r in parent['commands']),'Table source/audit not successful.')
    C=Path(parent['compiler']['path']);need(sha(C)==parent['compiler']['sha256'],'Compiler changed.')
    core=[r for r in parent['reused_modules'] if r['module']=='BusyBeaver.Core']
    table=[r for r in parent['fresh_modules'] if r['module']=='BusyBeaver.ZFC.TablePrefix246']
    need(len(core)==len(table)==1,'Unexpected table closure.')
    selected=[dict(core[0]),dict(module='BusyBeaver.ZFC.TablePrefix246',
        source=str(repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TablePrefix246.lean'),
        source_sha256=parent['source']['sha256'],object=table[0]['path'],object_sha256=table[0]['sha256'])]
    for r in selected:
        need(sha(Path(r['source']))==r['source_sha256'] and sha(Path(r['object']))==r['object_sha256'],'Parent provider changed.')
    need(imports(Path(selected[0]['source']))==[] and imports(Path(selected[1]['source']))==['BusyBeaver.Core'],
        'Selected project import closure changed.')
    need(imports(S)==['BusyBeaver.ZFC.TablePrefix246'] and imports(A)==[MODULE],'New imports changed.')
    st=S.read_text();at=A.read_text()
    need(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',st),'Forbidden proof shortcut.')
    need(not re.search(r'set_option\s+max(Heartbeats|RecDepth)',st+at),'Keep default proof limits.')
    need(re.findall(r'^#print axioms (.+)$',at,re.M)==PROBES and len(re.findall(r'^example\b',at,re.M))==4,
        'Audit contract changed.')
    W.mkdir(parents=True,exist_ok=True);cache=W/'cache';actual=[]
    for r in selected:
        dest=cache/Path(r['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        dest.symlink_to(Path(r['object']).resolve())
        actual.append(dict(module=r['module'],actual_first=str(dest),resolved=str(dest.resolve()),sha256=sha(dest)))
    snap=W/'sources'/Path(MODULE.replace('.','/')).with_suffix('.lean');snap.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(S,snap);aud=W/'Audit.lean';shutil.copyfile(A,aud)
    init=C.parent.parent/'lib/lean/Init.olean'
    inherited_init=[t for t in parent['toolchain_providers'] if t['module']=='Init']
    need(len(inherited_init)==1 and sha(init)==inherited_init[0]['object_sha256'],'Supplied Init boundary changed.')
    files=[Path(__file__).resolve(),HERE/'generate_fast_prefix246.py',HERE/'candidate-prefix246/zfc_prefix246.tm',
        S,A,P,C,init]+[Path(r[k]) for r in selected for k in ['source','object']]
    files=list(dict.fromkeys(files));before={str(p):sha(p) for p in files}
    record=dict(status='PREPARED_NOT_BUILT' if a.prepare_only else 'RUNNING',
        scope='Balanced exact246 transition table and equality to checked canonical machine; no bootstrap/runtime endpoint.',
        source=dict(path=str(S),sha256=sha(S),snapshot=str(snap)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aud)),
        compiler=parent['compiler'],compiler_version_query_performed=False,
        parent_evidence=[dict(path=str(P),sha256=sha(P))],reused_modules=selected,actual_first_providers=actual,
        toolchain_providers=[dict(module='Init',object=str(init),object_sha256=sha(init),scope='Supplied implicit toolchain boundary.')],
        exact_project_import_closure=True,LEAN_PATH=str(cache),commands=[],fresh_modules=[],before=before,
        limits=dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults'),
        dependency_build=False,downloads=False)
    def save():(W/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    def post():
        record['after']={str(p):sha(p) for p in files};need(before==record['after'],'Input/provider changed.')
        need(sha(snap)==SOURCE_SHA and sha(aud)==AUDIT_SHA,'Snapshot changed.')
        record['all_input_provider_postchecks']=True
    save()
    if a.prepare_only:post();save();print(W/'verification.json');return
    env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1');deadline=time.monotonic()+120
    def run(label,command):
        t=time.monotonic();remaining=deadline-t;need(remaining>0,'Shared wall budget exhausted.')
        log=W/(label+'.log')
        try:r=subprocess.run(command,cwd=W,env=env,capture_output=True,text=True,timeout=remaining)
        except subprocess.TimeoutExpired as e:
            dec=lambda x:x.decode(errors='replace') if isinstance(x,bytes) else(x or '')
            output=dec(e.stdout)+dec(e.stderr);log.write_text(output)
            record['commands'].append(dict(label=label,command=command,cwd=str(W),exit_code=None,timed_out=True,
                seconds=time.monotonic()-t,log=str(log),output=output));save();raise
        output=r.stdout+r.stderr;log.write_text(output)
        record['commands'].append(dict(label=label,command=command,cwd=str(W),exit_code=r.returncode,
            seconds=time.monotonic()-t,log=str(log),output=output));save()
        need(r.returncode==0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output,label+' failed.')
        return output
    try:
        obj=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        out=run('source',[str(C),'-j1','-M4096','--root='+str(W/'sources'),'-o',str(obj),str(snap)])
        need(obj.is_file() and not obj.is_symlink(),'Fresh object missing.')
        fresh=dict(module=MODULE,path=str(obj),sha256=sha(obj),source_sha256=sha(snap))
        record['fresh_modules']=[fresh];record['source_object_recorded_before_audit']=True;save()
        audit_out=run('audit',[str(C),'-j1','-M4096',str(aud)])
        parsed=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",audit_out,re.S)
        need([n for n,b in parsed]==PROBES,'Missing/reordered audit reports.')
        axioms=[dict(name=n,axioms=[x.strip() for x in b.split(',') if x.strip()]) for n,b in parsed]
        need(all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in axioms),'Unexpected axiom.')
        need(sha(obj)==fresh['sha256'],'Fresh object changed during audit.');post()
        record.update(status='PASS',named_axiom_probes=2,callers=4,actual_axiom_sets=axioms,
            only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,
            warnings=dict(source=out.count('warning:'),audit=audit_out.count('warning:')))
    except Exception as error:
        record.update(status='FAIL',error=str(error))
        try:post()
        except Exception as e:record['postcheck_error']=str(e)
        save();raise
    save();print(W/'verification.json')

if __name__=='__main__':main()
