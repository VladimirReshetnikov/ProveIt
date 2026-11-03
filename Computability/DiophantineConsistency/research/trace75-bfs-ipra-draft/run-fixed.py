#!/usr/bin/env python3
"""Check fixed-port trace75 iPRA client on explicitly mixed providers."""
from hashlib import sha256
from pathlib import Path
import json,os,re,shutil,subprocess,sys,tempfile,time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
h=Path(__file__).resolve().parent
src=h/'Trace75BFSFixedIPRA.lean'
client_record=h/'observations/attempt01/terminal.json'
iff_record=h.parent/'trace75-bfs-model-iff-prototype/observations/modeliff-attempt02/terminal.json'
inventory=h/'overlay-inventory.json'
overlay=Path('/tmp/trace75-bfs-ipra-overlay-78hgnvd6')
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
lib=Path('/tmp/trace75-fresh-rebuild-yn60cw_0/lib')
pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
pins={client_record:'ebdbbfa570fd7f15ddbfb8dd29c64fbe5600c357ea359c7789da17b72b2ccc73',
      Path('/tmp/trace75-bfs-ipra-tpj8nxvp/Trace75BFSIPRA.olean'):'75d2988695d143e0e26035d0d977197c4aa1c43d29b671f525c823ec323b6212',
      inventory:'e946d50e281d5d6326f7e5d1824dbd69deac215def46e148ed0c5923fb6bb028',
      iff_record:'c2b163694d1617aee0e499abd72355740e5fcc0579c5ae5e20df57ab686f7f6b',
      Path('/tmp/trace75-bfs-modeliff-tybefjkq/Trace75BFSModelIff.olean'):'e97639a427341e14bea30db3fed307556bedff7e9dfa50c6710f89f5bbe5c863',
      Path('/tmp/trace75-modelsyntax-i60jel9j/Trace75BFSSyntax.olean'):'15c89721715979a0071a7e5fa1bfca8d4188fd38b22480f4008532a09b5e3e9c',
      Path('/tmp/direct90-ipra-join-b66u_qqo/lib/PositiveModelIPRAReferenceTranslated.olean'):'d285f286b99912f7936f004d9a2472b6d6cce2935db2285522561f987aa6e65b',
      Path('/tmp/direct90-ipra-join-b66u_qqo/lib/PositiveModelIPRAStandardAdapter.olean'):'1fb7efa7fe6adce191c37dd9fc457ca4af4dd02210b3a19e6ae110d46fea9ce5',
      Path('/tmp/direct90-ipra-join-b66u_qqo/lib/PositiveModelIPRAAdapter.olean'):'8955395f621d3b4445bbe56ad3660be21b4f2d3b15f15cb384340a163cd81c12',
      Path('/tmp/trace75-syntax-ql2wu2mb/DiophantineConsistency/TenPositiveTrace75Syntax.olean'):'8349c9a4d22b2bdd2b3cb475570430b1df30a8e7f4e5e8ede9f40fb13a361d68',
      lib/'Trace75Factors.olean':'1bae9331cfbca4e35cb48916f135b63eedc8b5c827f8f24ae6f12b2dff111975',
      lean:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
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
def check_overlay():
    inv=json.loads(inventory.read_text());ns=overlay/'DiophantineConsistency'
    need(inv['overlay']==str(overlay),'overlay mismatch')
    need(set(x.name for x in ns.iterdir())==set(name for name,_ in inv['entries']),'overlay inventory mismatch')
    for name,target in inv['entries']:
        link=ns/name;need(link.is_symlink() and os.readlink(link)==target,'overlay link mismatch '+name)
check_overlay()
attempt=os.environ.get('ATTEMPT','attempt01');need(re.fullmatch(r'attempt\d+',attempt),'attempt name')
obs=h/'observations'/('fixed-'+attempt);need(not os.path.lexists(obs),'attempt exists')
pre=resources();need(len(pre['lean'])<2 and pre['mem_available_kib']>=8*1024**2,'resource preflight')
need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk guard')
obs.mkdir(parents=True);out=Path(tempfile.mkdtemp(prefix='trace75-bfs-iprafixed-'))
copy=out/src.name;shutil.copyfile(src,copy);shutil.copyfile(src,obs/'source.txt')
source_hash=sha(src);runner_hash=sha(Path(__file__))
cmd=[str(lean),'-M3000','-j1','-DElab.async=false',f'--root={out}',str(copy),'-o',str(out/'Trace75BFSFixedIPRA.olean')]
env={'PATH':'/usr/bin:/bin','LEAN_PATH':'/tmp/trace75-bfs-ipra-tpj8nxvp:'+json.loads(client_record.read_text())['lean_path'],'LEAN_NUM_THREADS':'1'}
expected={'Trace75BFSIPRA.olean':Path('/tmp/trace75-bfs-ipra-tpj8nxvp/Trace75BFSIPRA.olean'),'Trace75BFSModelIff.olean':Path('/tmp/trace75-bfs-modeliff-tybefjkq/Trace75BFSModelIff.olean'),'Trace75BFSSyntax.olean':Path('/tmp/trace75-modelsyntax-i60jel9j/Trace75BFSSyntax.olean'),'PositiveModelIPRAReferenceTranslated.olean':Path('/tmp/direct90-ipra-join-b66u_qqo/lib/PositiveModelIPRAReferenceTranslated.olean')}
def check_selection():
    roots=[Path(x) for x in env['LEAN_PATH'].split(':')]
    for name,target in expected.items():
        selected=next((r/name for r in roots if (r/name).is_file()),None)
        need(selected==target,'selection mismatch '+name)
check_selection()
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
output=(obs/'stdout').read_text()+(obs/'stderr').read_text();obj=out/'Trace75BFSFixedIPRA.olean'
names=['native_consistency','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency']
reports={name:re.findall(r"'Trace75BFSFixedIPRA\."+name+r"' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",output,re.S) for name in names}
ok=(proc.returncode==0 and reason is None and obj.is_file() and not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',output)
    and all(len(report)==1 and set(x.strip() for x in report[0].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'} for report in reports.values()))
need(sha(src)==source_hash==sha(copy)==sha(obs/'source.txt') and sha(Path(__file__))==runner_hash,'source/runner drift')
for p,digest in pins.items():need(sha(p)==digest,'pin changed '+str(p))
check_overlay()
check_selection()
record={'status':'PASS' if ok else 'FAILED','exit':proc.returncode,'reason':reason,'command':cmd,'lean_path':env['LEAN_PATH'],
        'source_sha256':source_hash,'runner_sha256':runner_hash,'pins':{str(p):{'sha256':d,'resolved':str(p.resolve())} for p,d in pins.items()},
        'output':str(obj),'output_sha256':sha(obj) if obj.is_file() else None,'stdout_sha256':sha(obs/'stdout'),'stderr_sha256':sha(obs/'stderr'),
        'preflight':pre,'samples':samples,'postflight':resources(),'scope':'exploratory fixed-port trace75 iPRA client; explicitly mixed old-first namespace provider with known graph/BFS drift; inherited remaining ancestry'}
(obs/'terminal.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':record['status'],'exit':record['exit'],'output':record['output'],'output_sha256':record['output_sha256']}))
raise SystemExit(0 if ok else 1)
