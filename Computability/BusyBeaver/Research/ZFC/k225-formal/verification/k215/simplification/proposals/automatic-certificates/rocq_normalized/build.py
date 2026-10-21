#!/usr/bin/env python3
"""Fresh serial Coq/Rocq build of the normalized source-equivalence closure."""
from pathlib import Path
import argparse, fcntl, hashlib, json, os, shutil, signal, subprocess, sys, time
ROOT=Path(__file__).resolve().parent
def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--out',type=Path,required=True)
ap.add_argument('--coqc',default='coqc')
ap.add_argument('--coqchk',default='coqchk')
ap.add_argument('--recursive',action='store_true')
args=ap.parse_args()
out=args.out.resolve()
if out.exists() and any(out.iterdir()):
    raise SystemExit('The output directory must initially be empty; no cached project objects are loaded.')
out.mkdir(parents=True,exist_ok=True)
work=out/'work';work.mkdir(exist_ok=True)
logs=out/'logs';logs.mkdir(exist_ok=True)
compiler=shutil.which(args.coqc);checker=shutil.which(args.coqchk)
assert compiler and checker
version=subprocess.check_output([compiler,'--version'],text=True).strip()
compat='version 8.18.' in version
assert compat or 'version 9.1.' in version, version
order=['Compat818.v'] if compat else []
order+=['deps/K230/RM.v','deps/K230/RMEquiv.v','deps/K230/Prog230.v',
        'deps/K230P/Bisim230.v','deps/K215F/Prog215.v','deps/K215F/DagPerm.v',
        'PathCodec.v','BisimMirror.v','NormalizedBisim.v',
        'NormalizedCert215.v','Source215Normalized.v']
flags=['-Q','deps/K230','K230','-Q','deps/K230P','K230P','-Q','deps/K215F','K215F']
record=dict(compiler=version,coqc_sha256=digest(compiler),coqchk_sha256=digest(checker),
            scope='exact all-register source equivalence; not the complete binary/ZFC endpoint',
            compatibility_aliases=compat,bindings=[],results=[])
for rel in order:
    src=ROOT/rel
    if rel=='deps/K230/RMEquiv.v':src=ROOT/'deps/K230/RMEquiv.rocq91.v'
    data=src.read_bytes()
    if compat and rel=='deps/K230/RMEquiv.v':
        before=b'From K230 Require Import RM.'
        assert data.count(before)==1
        data=data.replace(before,before+b'\nRequire Import Compat818.')
    dst=work/rel;dst.parent.mkdir(parents=True,exist_ok=True)
    if not dst.exists() or dst.read_bytes()!=data:dst.write_bytes(data)
    record['bindings'].append(dict(file=rel,source_sha256=digest(src),compiled_source_sha256=digest(dst)))
def run(name,cmd):
    print('CHECK',name,flush=True)
    logfile=logs/(name+'.log'); statfile=logs/(name+'.time')
    wrapped=[sys.executable,str(ROOT/'measure.py'),str(statfile),*cmd]
    start=time.monotonic()
    with Path('/tmp/proveit-k215-proof-build.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        t=time.monotonic()
        with logfile.open('w') as log:
            p=subprocess.Popen(wrapped,cwd=work,text=True,stdout=log,
                               stderr=subprocess.STDOUT,start_new_session=True)
            try:
                p.wait(timeout=900)
            except BaseException:
                os.killpg(p.pid,signal.SIGKILL)
                p.wait()
                raise
        seconds=time.monotonic()-t
    text=logfile.read_text()
    result=dict(name=name,argv=cmd,exit_code=p.returncode,proof_seconds=seconds,
                total_seconds=time.monotonic()-start,log_sha256=digest(logfile),
                closed_reports=text.count('Closed under the global context'),
                resource_report=statfile.read_text())
    record['results'].append(result)
    (out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    if p.returncode:
        print(text,flush=True); raise SystemExit(p.returncode)
    print('PASS',name,round(seconds,3),flush=True)
for rel in order:
    run(rel.replace('/','_'),[compiler,*flags,rel])
if args.recursive:run('coqchk_Source215Normalized',[checker,*flags,'-silent','Source215Normalized'])
record['status']='PASS_COMPILED_SOURCE_EQUIVALENCE'
record['recursive_source_check']='passed' if args.recursive else 'not requested'
record['build_driver_sha256']=digest(ROOT/'build.py')
(out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
print(record['status'],flush=True)
