#!/usr/bin/env python3
"""Check a trace73/75 restricted client on the captured fresh trace provider."""
from hashlib import sha256
from pathlib import Path
import json, os, re, shutil, subprocess, sys, tempfile, time

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('invoke python3 -I -S -B')
h = Path(__file__).resolve().parent
src = h/'Trace73PositiveBetaIff.lean'
lean = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
fresh = Path('/tmp/trace75-fresh-rebuild-yn60cw_0/lib')
pkg = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
roots = [Path('/tmp/trace73-iff-00auoa1w'), Path('/tmp/trace73-signs-7edju0w1'),
         Path('/tmp/trace73-model-caa17ucr'), Path('/tmp/trace73-literal-1adlrevr'),
         Path('/tmp/trace73-center-r4z617bq'), fresh, pkg]
pins = {
    lean: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    roots[0]/'Trace73RestrictedIff.olean': 'f328387a531b858239b7ebb452c9b50535417051b603910f3822f9f63659fe45',
    roots[1]/'Trace73ModelSigns.olean': 'fc3a5776eb50bccdb99874e90fd09242432a6540dc4156ac5d30bd3a98b440f9',
    roots[2]/'Trace73ModelTransfer.olean': '58fbf66066cf550957f7f24378dd943708b97750b26142164e224eaef214c930',
    roots[3]/'Trace73Literal.olean': 'e4bbe335d32f1f50ed2bfe2440c37f19a1f34ae4def4ff476b6e0778dfc3654d',
    roots[4]/'Trace73CenterV2.olean': 'fe3d39ec315888286a4d9d5ec2763badf338dc11bf141c0e19fa58f575de1e5a',
    fresh/'Trace75Transport.olean': 'c660d042eaa9e9e525d7bb0d09ca03651f2ec9b702a93f5bbd48da0e3c5ade54',
    fresh/'DiophantineConsistency/TenPositiveTrace75.olean': '1ae82441c7023e9675c5cc532d4026da6a3ee77e906996d67c315e4f693b079c',
    fresh/'DiophantineConsistency/ModelDifferenceRing.olean': 'd0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74',
    pkg/'Foundation/FirstOrder/Arithmetic/IOpen/Basic.olean': 'fdf05f04ff241ddea16128e1fc799cc5cc9470fbc1a63c92a200688ee597ef45',
}
def sha(p): return sha256(Path(p).read_bytes()).hexdigest()
def need(ok, reason):
    if not ok: raise RuntimeError(reason)
def resources():
    rows = subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines()
    active = [x.strip() for x in rows if len(x.split(None,3)) == 4 and x.split(None,3)[1]=='lean']
    mem = int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])
    return {'time_ns':time.time_ns(), 'lean':active, 'mem_available_kib':mem}
for p, digest in pins.items(): need(p.is_file() and sha(p)==digest, 'pin mismatch '+str(p))
attempt = os.environ.get('ATTEMPT','attempt01')
need(re.fullmatch(r'attempt\d+',attempt), 'bad attempt')
obs = h/'observations'/attempt
need(not os.path.lexists(obs), 'attempt exists')
pre = resources(); need(len(pre['lean']) < 2 and pre['mem_available_kib'] >= 8*1024**2, 'resource preflight')
need(shutil.disk_usage('/tmp').free >= 4*1024**3, 'disk guard')
obs.mkdir(parents=True); out = Path(tempfile.mkdtemp(prefix='trace73-positive-beta-'))
source = out/src.name; shutil.copyfile(src,source); shutil.copyfile(src,obs/'source.txt')
source_hash = sha(src); runner_hash = sha(Path(__file__))
cmd = [str(lean),'-M3000','-j1','-DElab.async=false',f'--root={out}',str(source),'-o',str(out/'Trace73PositiveBetaIff.olean')]
env = {'PATH':'/usr/bin:/bin', 'LEAN_PATH':':'.join(map(str,roots)), 'LEAN_NUM_THREADS':'1'}
samples=[]; reason=None; start=time.monotonic()
with (obs/'stdout').open('x') as so, (obs/'stderr').open('x') as se:
    proc=subprocess.Popen(cmd,env=env,stdout=so,stderr=se)
    while proc.poll() is None:
        s=resources(); samples.append(s)
        if len(s['lean'])>2 or s['mem_available_kib']<8*1024**2: reason='resource guard'; proc.terminate(); break
        if time.monotonic()-start>180: reason='timeout'; proc.terminate(); break
        time.sleep(2)
    try: proc.wait(timeout=10)
    except subprocess.TimeoutExpired: proc.kill(); proc.wait()
text=(obs/'stdout').read_text()+(obs/'stderr').read_text()
obj=out/'Trace73PositiveBetaIff.olean'
ok=proc.returncode==0 and reason is None and obj.is_file() and not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',text)
for name in ['shift_nonneg_of_positive_zero','positive_beta_restricted_iff']:
    reports=re.findall(r"'Trace73PositiveBetaIff\."+name+r"' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",text,re.S)
    ok=ok and len(reports)==1 and set(x.strip() for x in reports[0].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
need(sha(src)==source_hash==sha(source)==sha(obs/'source.txt') and sha(Path(__file__))==runner_hash, 'source or runner drift')
for p,digest in pins.items(): need(sha(p)==digest,'pin changed '+str(p))
record={'status':'PASS' if ok else 'FAILED','exit':proc.returncode,'reason':reason,'command':cmd,'lean_path':env['LEAN_PATH'],
        'source_sha256':source_hash,'runner_sha256':runner_hash,'pins':{str(p):{'sha256':digest,'resolved':str(p.resolve())} for p,digest in pins.items()},
        'output':str(obj),'output_sha256':sha(obj) if obj.exists() else None,'stdout_sha256':sha(obs/'stdout'),'stderr_sha256':sha(obs/'stderr'),
        'preflight':pre,'samples':samples,'postflight':resources(),'scope':'positive-beta 75 shift sign and restricted 73/75 iff; strict center and 73 shift sign remain hypotheses; inherited project/package/dynamic ancestry'}
(obs/'terminal.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':record['status'],'exit':record['exit'],'output':record['output'],'output_sha256':record['output_sha256']}))
raise SystemExit(0 if ok else 1)
