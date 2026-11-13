#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-mc-compose-core-retry-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='b7a17c838e41e4859d32d76d20e214edcd7e074366db0b0a63baaeacc5cc3edf' and sha(p/'source-manifest.json')=='5917b020b815448508059650cc8843f13fcb486d186c0c31deb641ff6054574c'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];runs=json.loads((root/'research/nine-sharing-sign17-mc-radix-runs-retry02-check/source-manifest.json').read_text())['rows'];chunk=json.loads((root/'research/nine-sharing-sign17-mc-chunk-check/source-manifest.json').read_text())['rows'];assert len(rows)==19 and rows[:17]==runs and rows[17]==chunk[15]
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==e['imports'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',src.read_text())
assert rows[-1]['imports']==['DiophantineConsistency.Sign17MCRadixRuns','DiophantineConsistency.Sign17MCChunks'];s=(p/'src/DiophantineConsistency/Sign17MCComposeCore.lean').read_text();assert all(t in s for t in ('digits.length = 8 ∧ bytes.length = 47','theorem radix_alignment : radix ^ 8 = (256 : ℕ) ^ 47','theorem aligned_repeat','theorem aligned_append','theorem flatten_tail','(ht : Nat.ofDigits radix xs = Nat.ofDigits 256 ys)'));assert (2**47)**8==256**47
old=root/'research/nine-sharing-sign17-mc-compose-core-check';oldrows=json.loads((old/'source-manifest.json').read_text())['rows'];assert rows[:18]==oldrows[:18]
oldsrc=(old/'src/DiophantineConsistency/Sign17MCComposeCore.lean').read_text();assert oldsrc.replace('    simp only [List.flatten_cons', '    simp only [Nat.ofDigits_append] at ih\n    simp only [List.flatten_cons',1)==s
oldrun=(old/'run.py').read_text();newrun=(p/'run.py').read_text();assert oldrun.replace('mc-compose-core-20261110','mc-compose-core-retry-20261110').replace('0c73c49f71772e8cea09ec1125f9d82328136db23e056335c0a3296f5eeecc17','5917b020b815448508059650cc8843f13fcb486d186c0c31deb641ff6054574c')==newrun
failure=root/'reviews/nine-sharing-sign17-mc-compose-core-terminal-independent/check.py';assert sha(failure)=='a6adae378806cc59ac0a8498560422f805cac2fd551c4ccdd71cc0849c55e3e7';subprocess.run([sys.executable,'-I','-S','-B',str(failure)],capture_output=True,check=True,timeout=120)
for label,pin in [('mc-radix-runs-retry02','e5032e47afbe135fb158b39cd445cd8b9d30e99ba3ca9fd403f25105d1a44a6b'),('mc-chunk','58313decc6226206b0d2032f3c65a4194890b3ff99d79c838532bcc839793390')]:
 c=root/('reviews/nine-sharing-sign17-'+label+'-terminal-independent/check.py');assert sha(c)==pin;subprocess.run([sys.executable,'-I','-S','-B',str(c)],check=True,capture_output=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and r.count('check_external_syntax()')>=3
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':19,'scope':'generic block composition proposal; no whole-port or file theorem'},indent=2))
