#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-mc-compose-core-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='eea4da8c1245449430688f7529af433fc92d51594627230c2bc0de6c356e8bc1' and sha(p/'source-manifest.json')=='0c73c49f71772e8cea09ec1125f9d82328136db23e056335c0a3296f5eeecc17'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];runs=json.loads((root/'research/nine-sharing-sign17-mc-radix-runs-retry02-check/source-manifest.json').read_text())['rows'];chunk=json.loads((root/'research/nine-sharing-sign17-mc-chunk-check/source-manifest.json').read_text())['rows'];assert len(rows)==19 and rows[:17]==runs and rows[17]==chunk[15]
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==e['imports'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',src.read_text())
assert rows[-1]['imports']==['DiophantineConsistency.Sign17MCRadixRuns','DiophantineConsistency.Sign17MCChunks'];s=(p/'src/DiophantineConsistency/Sign17MCComposeCore.lean').read_text();assert all(t in s for t in ('digits.length = 8 ∧ bytes.length = 47','theorem radix_alignment : radix ^ 8 = (256 : ℕ) ^ 47','theorem aligned_repeat','theorem aligned_append','theorem flatten_tail','(ht : Nat.ofDigits radix xs = Nat.ofDigits 256 ys)'));assert (2**47)**8==256**47
for label,pin in [('mc-radix-runs-retry02','e5032e47afbe135fb158b39cd445cd8b9d30e99ba3ca9fd403f25105d1a44a6b'),('mc-chunk','58313decc6226206b0d2032f3c65a4194890b3ff99d79c838532bcc839793390')]:
 c=root/('reviews/nine-sharing-sign17-'+label+'-terminal-independent/check.py');assert sha(c)==pin;subprocess.run([sys.executable,'-I','-S','-B',str(c)],check=True,capture_output=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and r.count('check_external_syntax()')>=3
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':19,'scope':'generic block composition proposal; no whole-port or file theorem'},indent=2))
