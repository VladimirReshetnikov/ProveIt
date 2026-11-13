#!/usr/bin/env python3
import gzip,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-mc-chunk-check';draft=root/'research/nine-sharing-sign17-mc-chunk-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='56fc7304eb692e2a2044867f584369365a130a19f384e0ec30d3ac185dabf5ba' and sha(p/'source-manifest.json')=='7151efc03ad765ac4928dcbfa089bba55ec8402377a50b0503cc58cd7029e662'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==16 and rows[:15]==prior
entry=rows[-1];src=p/'src/DiophantineConsistency/Sign17MCChunks.lean';assert sha(src)==sha(draft/src.name)==entry['source_sha256'] and entry['imports']==['DiophantineConsistency.Sign17ExactDegree'];s=src.read_text();assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';assert sha(seed)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';binding=json.loads(seed.read_text())['coefficient_binding'];rec=binding['ports']['MC'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()=='2b5c9296e32616260e64a051c92892645b9aa1bf0bf4c0d931e464080702ca9f' and len(raw)==11815
cases=[('all_selected',0,8),('boundary_951',118,8),('all_unselected',119,8),('boundary_986',123,8),('marker_1004',125,8),('final_3',251,3)];support=set(range(951))|set(range(960,986))|{1004};assert len(re.findall(r'^theorem ',s,re.M))==6
for name,index,count in cases:
 m=re.search(r'theorem '+name+r' :\s*Nat.ofDigits CurrentMasks2011.radix \[([^]]*)\] =\s*Nat.ofDigits 256 \[([^]]*)\] := by\s*unfold CurrentMasks2011.radix\s*decide \+kernel',s);assert m
 offsets=[int(z.strip().removeprefix('CurrentMasks2011.radix - ')) for z in m[1].split(',')];bs=bytes(int(z.strip()) for z in m[2].split(','));assert offsets==[2 if i in support else 1 for i in range(8*index,8*index+count)] and bs==raw[::-1][47*index:47*(index+1)] and len(bs)==(47 if count==8 else 18)
 value=sum(((1<<47)-o)*(1<<47)**i for i,o in enumerate(offsets));assert value==int.from_bytes(bs,'little')
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and r.count('check_external_syntax()')>=3
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','chunks':6,'scope':'local block equalities with external fixture check; no Lean file or whole-port theorem'},indent=2))
