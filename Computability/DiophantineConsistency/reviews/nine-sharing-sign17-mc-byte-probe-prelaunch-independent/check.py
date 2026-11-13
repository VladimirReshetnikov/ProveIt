#!/usr/bin/env python3
import gzip,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign17-mc-byte-probe-check';draft=root/'research/nine-sharing-sign17-mc-byte-probe-draft';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(packet/'run.py')=='824b8a2735f9c73d4c93192e781c45c4a9a0f48a90a2f59d8321fc937198d635'
assert sha(packet/'source-manifest.json')=='d7365879a11067aedda46ceb72c0ff8334575cb45f5913487943ac63bf0408a9'
assert sha(draft/'generate.py')=='2735f3937b805c586750a0216f09ed12acd04ec66ae5cfb0ccbca9ac25abd80a'
rows=json.loads((packet/'source-manifest.json').read_text())['rows']; prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==16 and rows[:15]==prior
src=packet/'src/DiophantineConsistency/Sign17MCByteLiteral.lean';assert sha(src)==sha(draft/src.name)==rows[-1]['source_sha256']=='de14ab2a18d560eb71022a5dc518129bc596206c6827c07789760e2b579ea4c6'
s=src.read_text();m=re.findall(r'^def mcLiteral : ℕ := 0x([0-9a-f]+)$',s,re.M);assert len(m)==1 and len(m[0])==23630
seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';assert sha(seed)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';binding=json.loads(seed.read_text())['coefficient_binding'];record=binding['ports']['MC'];packed=(seed.parent/binding['path']/record['file']).read_bytes();raw=gzip.decompress(packed)
assert hashlib.sha256(packed).hexdigest()=='b178777ae605e6d0073c824c48237e89e9b28911a2583bce7c6689a50ce3cdfd';assert len(raw)==11815 and hashlib.sha256(raw).hexdigest()=='2b5c9296e32616260e64a051c92892645b9aa1bf0bf4c0d931e464080702ca9f';assert bytes.fromhex(m[0])==raw
for t in ('theorem low_port_literal : CurrentMasks2011.lowPort = mcLiteral','theorem current_port2_literal : CurrentWindowCarry2011.ports 2 = (mcLiteral : ℤ)','decide +kernel','set_option maxRecDepth 100000 in','set_option maxHeartbeats 4000000 in'):assert t in s
assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
r=(packet/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and r.count('check_external_syntax()')>=3
x=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','literal_hex_digits':len(m[0]),'raw_bytes':len(raw),'scope':'proposed symbolic literal equality only; external bytes provenance separate'},indent=2))
