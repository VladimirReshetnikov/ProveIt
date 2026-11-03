#!/usr/bin/env python3
"""Bounded author-only QCube92 algebra check with selected-provider guards."""
from pathlib import Path
from hashlib import sha256
import json, os, shutil, subprocess, sys, tempfile, time

if sys.flags.optimize: raise SystemExit('optimized Python refused')
HERE=Path(__file__).resolve().parent
ATTEMPT=os.environ.get('ATTEMPT','attempt01')
ATTEMPT='existence-'+ATTEMPT
if not ATTEMPT.startswith('existence-attempt') or not ATTEMPT[17:].isdigit(): raise SystemExit('invalid attempt')
OBS=HERE/'observations'/ATTEMPT
if OBS.exists():raise SystemExit('refusing to overwrite attempt')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
ROOTS=[Path('/tmp/free-j-qcube92-eoo_i0bt'),
       Path('/tmp/free-j-qcube92-2gkx77ri'),
       Path('/tmp/free-j-qcube92-y12z83is'),
       Path('/tmp/free-j-sum-squares-author-zqexnf1s'),
       Path('/tmp/free-j-ordinary-tail-witness-author-cdbrbrco'),
       Path('/tmp/free-j-completeness-factor-author-q9rapr3k'),
       Path('/tmp/ipra-freej-signed-transport-replay-01/author'),
       Path('/tmp/ipra-ordinary12-coexistence-pair-01/author/child-output/lib')]
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')

def digest(p):return sha256(p.read_bytes()).hexdigest()
def resource():
    lines=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines()
    ps=[]
    for line in lines:
        fields=line.strip().split(None,3)
        if len(fields)==4 and fields[1]=='lean':ps.append({'pid':int(fields[0]),'rss_kib':int(fields[2]),'args':fields[3]})
    m=next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
    return {'time_ns':time.time_ns(),'mem_available_kib':int(m.split()[1]),'lean':ps}
def inventory():
    out={}
    for root in ROOTS:
        if not root.is_dir():raise RuntimeError('missing provider '+str(root))
        for path in sorted(root.rglob('*.olean')):
            if not path.is_file():raise RuntimeError('missing provider object '+str(path))
            out[str(path)]={'sha256':digest(path),'realpath':str(path.resolve())}
    return out
initial=resource()
if initial['mem_available_kib']<8*1024**2 or len(initial['lean'])>=2: raise SystemExit('resource guard refused launch')
if shutil.disk_usage('/tmp').free<4*1024**3:raise SystemExit('disk guard refused launch')
selected_before=inventory();source=HERE/'QCube92Existence.lean'; before={str(p):digest(p) for p in [source,HERE/'candidate.json',HERE/'check_graph.py',HERE/'run-existence.py',LEAN]}
OBS.mkdir(parents=True);out=Path(tempfile.mkdtemp(prefix='free-j-qcube92-')); local=out/'QCube92Existence.lean';shutil.copyfile(source,local)
env={'PATH':'/usr/bin:/bin','LEAN_PATH':':'.join(map(str,ROOTS+[PACKAGE])),'LEAN_NUM_THREADS':'1'}
cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={out}',str(local),'-o',str(out/'QCube92Existence.olean')]
samples=[];start=time.monotonic();reason=None
with (out/'stdout').open('x') as so,(out/'stderr').open('x') as se:
    proc=subprocess.Popen(cmd,env=env,stdout=so,stderr=se,text=True)
    while proc.poll() is None:
        snap=resource();samples.append(snap)
        if snap['mem_available_kib']<8*1024**2 or len(snap['lean'])>2:
            reason='resource guard';proc.kill();break
        if time.monotonic()-start>180:reason='timeout';proc.kill();break
        time.sleep(2)
    proc.wait()
stdout=(out/'stdout').read_text();stderr=(out/'stderr').read_text(); (OBS/'stdout').write_text(stdout);(OBS/'stderr').write_text(stderr)
selected_after=inventory();after={str(p):digest(p) for p in [source,HERE/'candidate.json',HERE/'check_graph.py',HERE/'run-existence.py',LEAN]}
obj=out/'QCube92Existence.olean'
result={'command':cmd,'lean_path':env['LEAN_PATH'],'output_root':str(out),'exit':proc.returncode,'reason':reason,'elapsed':time.monotonic()-start,'before':before,'after':after,'selected_provider_before':selected_before,'selected_provider_unchanged':selected_before==selected_after,'preflight':initial,'samples':samples,'object_sha256':digest(obj) if obj.is_file() else None,'stdout_sha256':digest(OBS/'stdout'),'stderr_sha256':digest(OBS/'stderr'),'scope':'Author-only selected-provider check; no complete inherited or package ancestry.'}
(OBS/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:result[k] for k in ('exit','reason','elapsed','output_root','object_sha256','selected_provider_unchanged')}));print(stdout);print(stderr,file=sys.stderr)
if proc.returncode!=0 or reason or before!=after or selected_before!=selected_after or not obj.is_file() or any(t in stdout+stderr for t in ('error:','warning:','sorryAx')):raise SystemExit(1)
