#!/usr/bin/env python3
import gzip,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-mf-chunk-check';draft=root/'research/nine-sharing-sign17-mf-chunk-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='8c493f1bf76a3680bcf351b76a80391d4181988f7a028f5f39ddcf8857e900a7' and sha(p/'source-manifest.json')=='42c674944f2e491f86152a218bd64e1bb8c183e26de95656c96fd69f30df5768'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==16 and rows[:15]==prior
entry=rows[-1];src=p/'src/DiophantineConsistency/Sign17MFChunks.lean';assert sha(src)==sha(draft/src.name)==entry['source_sha256']=='f7aa7519057ef3d63140210efb997bf601bdbcd6be7b6626044684c538818192' and entry['imports']==['DiophantineConsistency.Sign17ExactDegree'];s=src.read_text();assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';assert sha(seed)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';binding=json.loads(seed.read_text())['coefficient_binding'];rec=binding['ports']['MF'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert hashlib.sha256(packed).hexdigest()=='f04d074f8413c49581f262bcbb030c616f00745935010afc0d30050771627c3a' and hashlib.sha256(raw).hexdigest()=='5c15fc24e4978b878ed531abf30b2dcfe255083372034612b759b65eee1f0c25' and len(raw)==11815
digits=[3]+[8]*916+[0]*43+[1]*9+[0]*18+[1]*8+[0]*9+[1,2**45-4]+[0]*1005+[1];cases=[('first',0,8),('eights',1,8),('end_eights',114,8),('zeros',115,8),('ones',120,8),('end_ones',121,8),('start_ones',123,8),('end_ones2',124,8),('marker',125,8),('tail',251,4)];assert len(re.findall(r'^theorem ',s,re.M))==10
for name,index,count in cases:
 m=re.search(r'theorem '+name+r' :\s*Nat.ofDigits CurrentMasks2011.radix \[([^]]*)\] =\s*Nat.ofDigits 256 \[([^]]*)\] := by\s*unfold CurrentMasks2011.radix\s*decide \+kernel',s);assert m
 actual=[2**45-4 if x.strip()=='(2 ^ 45 - 4)' else int(x.strip()) for x in m[1].split(',')];bs=bytes(int(x.strip()) for x in m[2].split(','));assert actual==digits[8*index:8*index+count] and bs==raw[::-1][47*index:47*(index+1)] and len(bs)==(47 if count==8 else 18);assert sum(x*(1<<47)**i for i,x in enumerate(actual))==int.from_bytes(bs,'little')
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','chunks':10,'scope':'local MF block equalities only; no Lean file or whole-port theorem'},indent=2))
