#!/usr/bin/env python3
"""Rebuild the compact-certificate proofs and recursively kernel-check their targets.

No precompiled objects are used.  This builds the source correspondence and
certificate identity, not the complete 237-module ZFC machine endpoint.
"""
from pathlib import Path
import argparse, fcntl, hashlib, json, shutil, subprocess, time

ROOT=Path(__file__).resolve().parent
def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output',type=Path,default=ROOT/'verification')
args=ap.parse_args()
out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
work=out/'work';work.mkdir(exist_ok=True)
logs=out/'logs';logs.mkdir(exist_ok=True)
compiler=shutil.which('coqc');checker=shutil.which('coqchk')
assert compiler and checker,'coqc and coqchk must be on PATH'
version=subprocess.check_output([compiler,'--version'],text=True).strip()
compat='version 8.18.' in version
assert compat or 'version 9.1.' in version, 'Tested toolchain family required; see README'
order=['Compat818.v'] if compat else []
order+=['deps/K230/RM.v','deps/K230/RMEquiv.v','deps/K230/Prog230.v',
        'deps/K230P/Bisim230.v','deps/K215F/OffsetBisim230.v',
        'deps/K215F/Prog215.v','deps/K215F/DagPerm.v',
        'PathCodec.v','Cert215Compact.v','OriginalCert215.v','Cert215Exact.v',
        'BisimMirror.v','OffsetMirror.v','Source215Simple.v']
bindings=[]
for rel in order:
    source=ROOT/rel
    if rel=='deps/K230/RMEquiv.v':source=ROOT/'deps/K230/RMEquiv.rocq91.v'
    data=source.read_bytes()
    if compat and rel=='deps/K230/RMEquiv.v':
        # Only a library-compatibility import: all original code/proofs remain.
        before=b'From K230 Require Import RM.'
        assert data.count(before)==1
        data=data.replace(before,before+b'\nRequire Import Compat818.')
    target=work/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    bindings.append(dict(file=rel,source_sha256=digest(source),compiled_source_sha256=digest(target)))
flags=['-Q','deps/K230','K230','-Q','deps/K230P','K230P','-Q','deps/K215F','K215F']
record=dict(compiler=version,coqc_sha256=digest(compiler),coqchk_sha256=digest(checker),
            compatibility_aliases=compat,scope='source correspondence and exact certificate; not full ZFC endpoint',
            bindings=bindings,results=[])
def run(name,cmd):
    print('CHECK',name,flush=True)
    start=time.monotonic()
    with Path('/tmp/proveit-k215-proof-build.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        t=time.monotonic()
        p=subprocess.run(cmd,cwd=work,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        secs=time.monotonic()-t
    (logs/(name+'.log')).write_text(p.stdout)
    item=dict(name=name,argv=cmd,exit_code=p.returncode,proof_seconds=secs,
              total_seconds=time.monotonic()-start,log_sha256=digest(logs/(name+'.log')),
              closed_reports=p.stdout.count('Closed under the global context'))
    record['results'].append(item)
    (out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    if p.returncode:
        print(p.stdout)
        raise SystemExit(p.returncode)
    print('PASS',name,round(secs,3),flush=True)
for rel in order:run(rel.replace('/','_'),[compiler,*flags,rel])
for target in ['Cert215Exact','Source215Simple','OffsetMirror']:
    run('coqchk_'+target,[checker,*flags,'-silent',target])
for name in ['PathCodec.v','Cert215Exact.v','BisimMirror.v','OffsetMirror.v','Source215Simple.v']:
    r=next(r for r in record['results'] if r['name']==name)
    log=(logs/(name+'.log')).read_text()
    assert r['closed_reports']==2 and 'Axioms:' not in log, (name,log)
record['status']='PASS_CLOSED_SOURCE_AND_CERTIFICATE'
(out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
print(record['status'],flush=True)
