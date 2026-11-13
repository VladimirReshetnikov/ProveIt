#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-mc-radix-runs-check';draft=root/'research/nine-sharing-sign17-mc-radix-runs-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='e5835d39277d0049a384e6135fefa8d3dcb6633ea29ad8b9d50e4bfaac184394' and sha(p/'source-manifest.json')=='fcf611a47b5689049d80c20f8ac0a08686c6b2b0f3013e06aa02ecb3b6787a6c'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==16 and rows[:15]==prior
entry=rows[-1];src=p/'src/DiophantineConsistency/Sign17MCRadixRuns.lean';assert sha(src)==sha(draft/src.name)==entry['source_sha256']=='bd70e53dbd6f0fc6617e30c142cf6f7188b98cc9bc40d38812a846c1a7fc07cf' and entry['imports']==['DiophantineConsistency.Sign17ExactDegree'];s=src.read_text();assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
runs=[(int(a),int(b)) for a,b in re.findall(r'List.replicate (\d+) \(radix - (\d+)\)',s)];assert runs==[(951,2),(9,1),(26,2),(18,1),(1,2),(1006,1)];digits=[v for count,v in runs for _ in range(count)];assert len(digits)==2011 and {i for i,v in enumerate(digits) if v==2}==set(range(951))|set(range(960,986))|{1004}
for x in ('theorem maskList_runs : LowMaskCoding.maskList radix 2 2011 lowSupport = runs','theorem low_port_runs : lowPort = Nat.ofDigits radix runs','LowMaskCoding.ofDigits_maskList','CurrentMasks2011.lowSupport_def','split_ifs <;> omega'):assert x in s
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and r.count('check_external_syntax()')>=3
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','digits':2011,'scope':'proposed symbolic mask digit runs only, no Lean result or byte/file theorem'},indent=2))
