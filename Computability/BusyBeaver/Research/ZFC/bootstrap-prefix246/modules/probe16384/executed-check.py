#!/usr/bin/env python3
"""Bounded local16384 exact246 calculation; no blank-start identification.

Reuses checked FastTablePrefix246, TablePrefix246 and Core, plus exact
FiniteZipper from the successful MP-control boundary. Explicit Init/Omega
supplied toolchain boundaries; no dependency build/download/version query.
Serial -j1 -M4096, default proof limits, shared120s source/audit budget.
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
REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
SOURCE_SHA='9976745e2c9380102e37dea114b257cd98575f152ce1e71538f2eb1608882993'
AUDIT_SHA='b53f558f651347d47384439fe62b9cbd07c61273be1660c4efa536eccb40b322'
PARENT_SHA='e048c1f6dfca04de875e48344e2c4f2a4fb4d2d0ea7562c87f23f4cd433ba850'
ZIPPER_RECORD_SHA='92c2bddc7390806e81b30daa15c2bcfe082dcae6555392a57fe6d1ae987df81b'
PROBES=['SetTheory.BusyBeaver.ZFC.BootPrefix246Probe16384.'+n for n in ['local16384','transfer16384']]
MODULE='BusyBeaver.ZFC.BootPrefix246Probe16384'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(c,m):
    if not c:raise RuntimeError(m)
def imports(p):return re.findall(r'^import\s+(\S+)\s*$',p.read_text(),re.M)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=REPO)
    ap.add_argument('--source',type=Path,default=HERE/'BootPrefix246Probe16384.lean')
    ap.add_argument('--audit',type=Path,default=HERE/'Audit.lean')
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--prepare-only',action='store_true')
    a=ap.parse_args();repo=a.repo.resolve();S=a.source.resolve();A=a.audit.resolve();W=a.output.resolve()
    need(not W.is_relative_to(repo) and (not W.exists() or not any(W.iterdir())),'Use new/empty external output.')
    need(sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA,'Source or audit changed.')
    P=HERE.parent/'fast/run1/verification.json'
    need(sha(P)==PARENT_SHA,'Selected fast-table parent changed.')
    parent=json.loads(P.read_text());need(parent['status']=='PASS' and parent['named_axiom_probes']==2 and
        parent['callers']==4 and parent['only_standard_axioms'] and parent['all_input_provider_postchecks'] and
        parent['all_fresh_objects_unchanged_after_audit'],'Incomplete successful fast-table parent.')
    need([r['label'] for r in parent['commands']]==['source','audit'] and
        all(r['exit_code']==0 for r in parent['commands']),'Fast-table source/audit not successful.')
    C=Path(parent['compiler']['path']);need(sha(C)==parent['compiler']['sha256'],'Compiler changed.')
    Z=repo/'Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-mp254-verification.json'
    need(sha(Z)==ZIPPER_RECORD_SHA,'Selected zipper boundary record changed.')
    zp=json.loads(Z.read_text());need(zp['status']=='PASS' and zp['all_input_provider_postchecks'] and
        zp['all_fresh_objects_unchanged_after_audit'] and zp['only_standard_axioms'],'Incomplete zipper boundary.')
    need(zp['compiler']['sha256']==parent['compiler']['sha256'],'Mixed compilers.')
    selected=[dict(r) for r in parent['reused_modules']]
    need([r['module'] for r in selected]==['BusyBeaver.Core','BusyBeaver.ZFC.TablePrefix246'],'Unexpected fast ancestry.')
    fast=[r for r in parent['fresh_modules'] if r['module']=='BusyBeaver.ZFC.FastTablePrefix246']
    zipper=[r for r in zp['reused_modules'] if r['module']=='BusyBeaver.ZFC.FiniteZipper']
    omega=[r for r in zp['toolchain_providers'] if r['module']=='Lean.Elab.Tactic.Omega']
    need(len(fast)==len(zipper)==len(omega)==1,'Ambiguous required providers.')
    selected.append(dict(module='BusyBeaver.ZFC.FastTablePrefix246',
        source=parent['source']['path'],
        source_sha256=parent['source']['sha256'],object=fast[0]['path'],object_sha256=fast[0]['sha256']))
    selected.append(dict(zipper[0]))
    for r in selected:
        need(sha(Path(r['source']))==r['source_sha256'] and sha(Path(r['object']))==r['object_sha256'],'Parent provider changed.')
    need(imports(Path(selected[0]['source']))==[] and imports(Path(selected[1]['source']))==['BusyBeaver.Core'] and
        imports(Path(selected[2]['source']))==['BusyBeaver.ZFC.TablePrefix246'] and
        imports(Path(selected[3]['source']))==['Lean.Elab.Tactic.Omega','BusyBeaver.Core'],
        'Selected project import closure changed.')
    need(imports(S)==['BusyBeaver.ZFC.FastTablePrefix246','BusyBeaver.ZFC.FiniteZipper'] and
        imports(A)==[MODULE],'New imports changed.')
    O=Path(omega[0]['object']);need(sha(O)==omega[0]['object_sha256'],'Supplied Omega boundary changed.')
    need(O.resolve()==(C.parent.parent/'lib/lean/Lean/Elab/Tactic/Omega.olean').resolve(),
        'Omega is not the selected compiler toolchain provider.')
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
    inherited_init=[r for r in parent['toolchain_providers'] if r['module']=='Init']
    need(len(inherited_init)==1 and sha(init)==inherited_init[0]['object_sha256'],'Supplied Init boundary changed.')
    files=[Path(__file__).resolve(),HERE/'generate.py',HERE/'data.json',repo/'Computability/BusyBeaver/Research/ZFC/candidate-prefix246/zfc_prefix246.tm',
        S,A,P,Z,C,init,O]+[Path(r[k]) for r in selected for k in ['source','object']]
    files=list(dict.fromkeys(files));before={str(p):sha(p) for p in files}
    record=dict(status='PREPARED_NOT_BUILT' if a.prepare_only else 'RUNNING',
        scope='Local16384 calculation on explicit long tape and conditional whole-tape transport; no theorem connects its start to blank execution.',
        source=dict(path=str(S),sha256=sha(S),snapshot=str(snap)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aud)),
        compiler=parent['compiler'],compiler_version_query_performed=False,
        parent_evidence=[dict(path=str(P),sha256=sha(P)),dict(path=str(Z),sha256=sha(Z))],reused_modules=selected,actual_first_providers=actual,
        toolchain_providers=[dict(module='Init',object=str(init),object_sha256=sha(init),scope='Supplied implicit toolchain boundary.'),
            dict(module='Lean.Elab.Tactic.Omega',object=str(O),object_sha256=sha(O),scope='Supplied toolchain boundary from exact MP-control record.')],
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
