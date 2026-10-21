#!/usr/bin/env python3
"""Fresh serial source-only build; no cached proof objects or network needed.

This checks source correspondence, not the full K215 machine/ZFC endpoint.
"""
from pathlib import Path
import argparse, fcntl, hashlib, json, shutil, subprocess, time

ROOT = Path(__file__).resolve().parent
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output', type=Path, default=ROOT/'fresh-build')
ap.add_argument('--benchmark', action='store_true', help='Also compile the incoming plain-list baseline')
ap.add_argument('--check-generic', action='store_true', help='Recursively coqchk the generic checker and its dependencies')
args = ap.parse_args()
out = args.output.resolve()
if out.exists() and any(out.iterdir()):
    raise SystemExit('Choose an empty output directory; saved evidence is never overwritten.')
out.mkdir(parents=True, exist_ok=True)
work=out/'work'; logs=out/'logs'; work.mkdir(); logs.mkdir()
coqc=shutil.which('coqc'); coqchk=shutil.which('coqchk')
assert coqc, 'coqc is required'
version=subprocess.check_output([coqc,'--version'],text=True).strip()
compat='version 8.18.' in version
assert compat or 'version 9.1.' in version, 'Use recorded Coq 8.18 or the untested-in-this-packet Rocq 9.1 integration branch'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
order=['Compat818.v'] if compat else []
order += ['deps/K230/RM.v','deps/K230/RMEquiv.v','deps/K230/Prog230.v',
          'deps/K230P/Bisim230.v','deps/K215F/Prog215.v','deps/K215F/DagPerm.v',
          'PathCodec.v','Cert215Compact.v','BisimMirror.v','BalancedBisim.v',
          'Cert215Tree.v','Source215Balanced.v']
if args.benchmark: order += ['Source215Simple.v']
flags=['-Q','deps/K230','K230','-Q','deps/K230P','K230P','-Q','deps/K215F','K215F']
record={'compiler':version,'coqc_sha256':sha(coqc),'scope':'K215 source correspondence only',
        'compatibility_import':compat,'fresh_build':True,'results':[]}
for rel in order:
    source=ROOT/rel
    if rel=='deps/K230/RMEquiv.v': source=ROOT/'deps/K230/RMEquiv.rocq91.v'
    data=source.read_bytes()
    if compat and rel=='deps/K230/RMEquiv.v':
        before=b'From K230 Require Import RM.'
        assert data.count(before)==1
        data=data.replace(before,before+b'\nRequire Import Compat818.')
    target=work/rel; target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(data)
    cmd=[coqc,*flags,rel]; print('COMPILE',rel,flush=True)
    with Path('/tmp/proveit-proof-compiler.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        start=time.monotonic()
        p=subprocess.run(cmd,cwd=work,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        elapsed=time.monotonic()-start
    log=logs/(rel.replace('/','_')+'.log'); log.write_text(p.stdout)
    rec={'file':rel,'argv':cmd,'exit_code':p.returncode,'seconds':elapsed,
         'input_sha256':sha(source),'compiled_source_sha256':sha(target),
         'log_sha256':sha(log),'closed_reports':p.stdout.count('Closed under the global context')}
    if p.returncode==0: rec['object_sha256']=sha(target.with_suffix('.vo'))
    record['results'].append(rec); (out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    if p.returncode:
        print(p.stdout); raise SystemExit(p.returncode)
    if rel in ['BalancedBisim.v','Cert215Tree.v','Source215Balanced.v']:
        assert rec['closed_reports']==2 and 'Axioms:' not in p.stdout, (rel,p.stdout)
    print('PASS',rel,round(elapsed,3),flush=True)
if args.check_generic:
    assert coqchk
    cmd=[coqchk,*flags,'-silent','BalancedBisim']
    with Path('/tmp/proveit-proof-compiler.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        start=time.monotonic()
        p=subprocess.run(cmd,cwd=work,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        elapsed=time.monotonic()-start
    log=logs/'coqchk_BalancedBisim.log'; log.write_text(p.stdout)
    record['recursive_generic_check']={'argv':cmd,'exit_code':p.returncode,
        'seconds':elapsed,'log_sha256':sha(log),'coqchk_sha256':sha(coqchk)}
    (out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    if p.returncode: print(p.stdout); raise SystemExit(p.returncode)
record['status']='PASS_CLOSED_SOURCE_CORRESPONDENCE'
(out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
print(record['status'])
