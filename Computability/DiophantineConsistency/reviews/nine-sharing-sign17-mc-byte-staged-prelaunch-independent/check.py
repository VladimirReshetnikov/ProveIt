#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-mc-byte-staged-check';draft=root/'research/nine-sharing-sign17-mc-byte-staged-draft';old=root/'research/nine-sharing-sign17-mc-byte-probe-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='1d499302c9b3550a66424d1e8597ed0aaf5f75eaa3880cfae5f87f66214f8801' and sha(p/'source-manifest.json')=='2930672c9b14ddaeac99fe2c91fc188e3661b0f721e7213fb3c65cbc760dc31a'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];oldrows=json.loads((old/'source-manifest.json').read_text())['rows'];assert len(rows)==17 and rows[:15]==oldrows[:15]
for row in rows:
 src=p/'src/DiophantineConsistency'/(row['module'].split('.')[-1]+'.lean');assert sha(src)==row['source_sha256'];assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==row['imports']
for row in rows[-2:]:
 n=row['module'].split('.')[-1];assert sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(draft/(n+'.lean'))
decl=(draft/'Sign17MCLiteralDecl.lean').read_text();proof=(draft/'Sign17MCLiteralProof.lean').read_text();before=(old/'src/DiophantineConsistency/Sign17MCByteLiteral.lean').read_text();pattern=r'^def mcLiteral : ℕ := 0x([0-9a-f]+)$';assert re.findall(pattern,decl,re.M)==re.findall(pattern,before,re.M) and len(re.findall(pattern,decl,re.M)[0])==23630
assert 'theorem literal_refl : mcLiteral = mcLiteral := rfl' in decl
for n in ('low_port_literal','current_port2_literal'):
 pat=r'(?ms)^theorem '+n+r'\b.*?(?=\n\ntheorem|\n\nend)';assert re.search(pat,proof).group()==re.search(pat,before).group()
assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',decl+proof)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and r.count('check_external_syntax()')>=3
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':17,'scope':'diagnostic: literal declaration then unchanged finite comparison; no Lean result or file binding'},indent=2))
