#!/usr/bin/env python3
"""Compile the direct compiler and old-API adapter, with fresh project objects.

The toolchain standard library is used normally. No project object is reused in
the proposal build. A separate baseline target reuses only byte-identical
dependencies compiled in that first build, then recompiles original EnumPerm.
"""
from pathlib import Path
import argparse, fcntl, hashlib, json, os, re, shutil, subprocess, time

ap=argparse.ArgumentParser()
ap.add_argument('--repo',type=Path,required=True)
ap.add_argument('--lean',type=Path,required=True)
ap.add_argument('--out',type=Path,required=True)
a=ap.parse_args()
build_lock=open('/tmp/proveit-k215-proof-build.lock','a')
fcntl.flock(build_lock,fcntl.LOCK_EX)
here=Path(__file__).resolve().parent
out=a.out.resolve()
out.mkdir(parents=True,exist_ok=False)
roots=[here/'sources',a.repo/'Computability/BusyBeaver/Lean',a.repo/'Logic/FirstOrder/Lean']
seen=set();order=[]

def source(m):
    return next((r/(m.replace('.','/')+'.lean') for r in roots
                 if (r/(m.replace('.','/')+'.lean')).exists()),None)

def visit(m):
    if m in seen:return
    seen.add(m)
    if m=='Init':return
    p=source(m)
    if p is None:raise RuntimeError('Missing source '+m)
    for im in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):visit(im)
    order.append((m,p))

visit('CompilerFusionAudit')
visit('CompilerFusionCompatAudit')
src=out/'src';obj=out/'obj';logs=out/'logs'
for d in [src,obj,logs]:d.mkdir()
records=[]
env=dict(os.environ,LEAN_PATH=str(obj))
version=subprocess.check_output([str(a.lean),'--version'],text=True).strip()
for m,p in order:
    rel=Path(m.replace('.','/')+'.lean');s=src/rel;o=(obj/rel).with_suffix('.olean')
    s.parent.mkdir(parents=True,exist_ok=True);o.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(p,s)
    start=time.monotonic()
    proc=subprocess.run([str(a.lean),'-o',str(o),str(rel)],cwd=src,env=env,capture_output=True,text=True)
    elapsed=time.monotonic()-start
    log=logs/(m+'.log');log.write_text(proc.stdout+proc.stderr)
    rec={'module':m,'source_sha256':hashlib.sha256(s.read_bytes()).hexdigest(),
         'returncode':proc.returncode,'seconds':elapsed,'log':str(log.relative_to(out)),
         'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
    if o.exists():rec['olean_sha256']=hashlib.sha256(o.read_bytes()).hexdigest()
    records.append(rec)
    print(json.dumps({'module':m,'returncode':proc.returncode,'seconds':round(elapsed,3)}),flush=True)
    (out/'receipt.json').write_text(json.dumps({'toolchain':version,'records':records},indent=2)+'\n')
    if proc.returncode:
        print(proc.stdout+proc.stderr,flush=True)
        raise SystemExit(proc.returncode)

# Recompile the original module and explicit public-type client.
basesrc=out/'baseline-src';baseobj=out/'baseline-obj'
shutil.copytree(obj,baseobj)
path=Path('BusyBeaver/ZFC/EnumPerm.lean')
(basesrc/path).parent.mkdir(parents=True,exist_ok=True)
(baseobj/path).parent.mkdir(parents=True,exist_ok=True)
shutil.copyfile(a.repo/'Computability/BusyBeaver/Lean'/path,basesrc/path)
(basesrc/'BaselineAudit.lean').write_text('''import BusyBeaver.ZFC.EnumPerm
open SetTheory.BusyBeaver.ZFC
example {n : Nat} (h : KCodeDom.CDom n) : ∃ p : List EnumPerm.Cmd, EnumPerm.Contract p n :=
  EnumPerm.build h
example {s : EnumPerm.St} (hpl : s.pl = 0) (hs : EnumPerm.Inv (EnumPerm.toW s)) :
    EnumPerm.HaltsFrom s ↔ KCode222.C222 Code254.F := EnumPerm.halts_iff hpl hs
#print axioms EnumPerm.build
#print axioms EnumPerm.complete
#print axioms EnumPerm.halts_iff
''')
benv=dict(os.environ,LEAN_PATH=str(baseobj)+os.pathsep+str(obj))
brecords=[]
for m in ['BusyBeaver.ZFC.EnumPerm','BaselineAudit']:
    rel=Path(m.replace('.','/')+'.lean');o=(baseobj/rel).with_suffix('.olean')
    start=time.monotonic()
    proc=subprocess.run([str(a.lean),'-o',str(o),str(rel)],cwd=basesrc,env=benv,capture_output=True,text=True)
    elapsed=time.monotonic()-start
    log=logs/('baseline-'+m+'.log');log.write_text(proc.stdout+proc.stderr)
    brecords.append({'module':m,'returncode':proc.returncode,'seconds':elapsed,
      'source_sha256':hashlib.sha256((basesrc/rel).read_bytes()).hexdigest(),
      'log':str(log.relative_to(out)),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),
      'olean_sha256':hashlib.sha256(o.read_bytes()).hexdigest() if o.exists() else None})
    print(json.dumps({'baseline_module':m,'returncode':proc.returncode,'seconds':round(elapsed,3)}),flush=True)
    (out/'receipt.json').write_text(json.dumps({'toolchain':version,'records':records,
      'baseline_records':brecords,'baseline_reuse':'Only byte-identical dependency objects from proposal build'},indent=2)+'\n')
    if proc.returncode:print(proc.stdout+proc.stderr,flush=True);raise SystemExit(proc.returncode)
print('PASS',flush=True)
