#!/usr/bin/env python3
"""Check the graph-specific kappa/root bound on the fresh trace75 provider."""
from hashlib import sha256
from pathlib import Path
import json,os,re,shutil,subprocess,sys,tempfile,time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
h=Path(__file__).resolve().parent
src=h/'Trace75FixedTo73.lean'
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
lib=Path('/tmp/trace75-fresh-rebuild-yn60cw_0/lib')
pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
pins={lean:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
      Path('/tmp/trace75-normalize-qdmz3b0v/Trace75NormalizeCenter.olean'):'c9db6c31f50c7b19480d7f8f0653e053a77313b7765363ffdd5967b2f1195148',
      lib/'Trace75FixedBounds.olean':'036b410cf7f1242e45a829413b019742c56af2c480ded871ce88c2ef3f76e822',
      Path('/tmp/trace75-kapparoot-ewby3i34/Trace75KappaRoot.olean'):'ba694f90388cf52b3b692d4c590d59298fdc1b626c819246de0e228f3f3e10f1',
      Path('/tmp/trace75-signflip-5t6uw3qf/Trace75SignFlip.olean'):'853d9841662ae9ae17388da47c4cc684332e99cbdc3346035564c4997ade70af',
      Path('/tmp/trace73-signs-7edju0w1/Trace73ModelSigns.olean'):'fc3a5776eb50bccdb99874e90fd09242432a6540dc4156ac5d30bd3a98b440f9',
      Path('/tmp/trace73-model-caa17ucr/Trace73ModelTransfer.olean'):'58fbf66066cf550957f7f24378dd943708b97750b26142164e224eaef214c930',
      Path('/tmp/trace73-literal-1adlrevr/Trace73Literal.olean'):'e4bbe335d32f1f50ed2bfe2440c37f19a1f34ae4def4ff476b6e0778dfc3654d',
      Path('/tmp/trace73-center-r4z617bq/Trace73CenterV2.olean'):'fe3d39ec315888286a4d9d5ec2763badf338dc11bf141c0e19fa58f575de1e5a',
      lib/'Trace75IntegralTransport.olean':'75fb14d7da423b646a4e8197e0cd100e72f53458eab4e39042aea058c4493e54',
      lib/'Trace75OffsetExact.olean':'8b92370631be7284e641d6a8a27f0d78d9ae7e8f0e372f49d330c10c79d8970a',
      lib/'Trace75Kappa.olean':'d1b5f11393d947960986f70e247db55dbcc559a4fe7214878006f64a25f78b2a',
      lib/'DiophantineConsistency/TenPositiveTrace75.olean':'1ae82441c7023e9675c5cc532d4026da6a3ee77e906996d67c315e4f693b079c',
      lib/'DiophantineConsistency/ModelDifferenceRing.olean':'d0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74',
      pkg/'Foundation/FirstOrder/Arithmetic/IOpen/Basic.olean':'fdf05f04ff241ddea16128e1fc799cc5cc9470fbc1a63c92a200688ee597ef45'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b: raise RuntimeError(m)
def resources():
    lines=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines()
    active=[s.strip() for s in lines if len(s.split(None,3))==4 and s.split(None,3)[1]=='lean']
    mem=int(next(s for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')).split()[1])
    return {'time_ns':time.time_ns(),'lean':active,'mem_available_kib':mem}
for p,digest in pins.items():need(p.is_file() and sha(p)==digest,'pin mismatch '+str(p))
attempt=os.environ.get('ATTEMPT','attempt01');need(re.fullmatch(r'attempt\d+',attempt),'attempt name')
obs=h/'observations'/('fixed-'+attempt);need(not os.path.lexists(obs),'attempt exists')
pre=resources();need(len(pre['lean'])<2 and pre['mem_available_kib']>=8*1024**2,'resource preflight')
need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk guard')
obs.mkdir(parents=True);out=Path(tempfile.mkdtemp(prefix='trace75-fixedto73-'))
copy=out/src.name;shutil.copyfile(src,copy);shutil.copyfile(src,obs/'source.txt')
source_hash=sha(src);runner_hash=sha(Path(__file__))
cmd=[str(lean),'-M3000','-j1','-DElab.async=false',f'--root={out}',str(copy),'-o',str(out/'Trace75FixedTo73.olean')]
env={'PATH':'/usr/bin:/bin','LEAN_PATH':'/tmp/trace75-normalize-qdmz3b0v:/tmp/trace75-kapparoot-ewby3i34:/tmp/trace75-signflip-5t6uw3qf:/tmp/trace73-signs-7edju0w1:/tmp/trace73-model-caa17ucr:/tmp/trace73-literal-1adlrevr:/tmp/trace73-center-r4z617bq:'+str(lib)+':'+str(pkg),'LEAN_NUM_THREADS':'1'}
samples=[];reason=None;start=time.monotonic()
with (obs/'stdout').open('x') as so,(obs/'stderr').open('x') as se:
    proc=subprocess.Popen(cmd,env=env,stdout=so,stderr=se)
    while proc.poll() is None:
        sample=resources();samples.append(sample)
        if len(sample['lean'])>2 or sample['mem_available_kib']<8*1024**2:reason='resource guard';proc.terminate();break
        if time.monotonic()-start>180:reason='timeout';proc.terminate();break
        time.sleep(2)
    try:proc.wait(timeout=10)
    except subprocess.TimeoutExpired:proc.kill();proc.wait()
output=(obs/'stdout').read_text()+(obs/'stderr').read_text();obj=out/'Trace75FixedTo73.olean'
reports=re.findall(r"'Trace75FixedTo73\.positive_zero_to_center' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",output,re.S)
ok=(proc.returncode==0 and reason is None and obj.is_file() and not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',output)
    and len(reports)==1 and set(x.strip() for x in reports[0].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'})
need(sha(src)==source_hash==sha(copy)==sha(obs/'source.txt') and sha(Path(__file__))==runner_hash,'source/runner drift')
for p,digest in pins.items():need(sha(p)==digest,'pin changed '+str(p))
record={'status':'PASS' if ok else 'FAILED','exit':proc.returncode,'reason':reason,'command':cmd,'lean_path':env['LEAN_PATH'],
        'source_sha256':source_hash,'runner_sha256':runner_hash,'pins':{str(p):{'sha256':d,'resolved':str(p.resolve())} for p,d in pins.items()},
        'output':str(obj),'output_sha256':sha(obj) if obj.is_file() else None,'stdout_sha256':sha(obs/'stdout'),'stderr_sha256':sha(obs/'stderr'),
        'preflight':pre,'samples':samples,'postflight':resources(),'scope':'symbolic beta and masks yield 75-to-73 positive-zero implication for arbitrary kernel port; provider ancestry inherited'}
(obs/'terminal.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':record['status'],'exit':record['exit'],'output':record['output'],'output_sha256':record['output_sha256']}))
raise SystemExit(0 if ok else 1)
