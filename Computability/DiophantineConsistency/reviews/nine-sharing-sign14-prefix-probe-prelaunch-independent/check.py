#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-probe-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='5d62bfa707d05f350dae4a2ff30ce75ec20e2e267cf3fc245ccdc40a613daea0' and sha(p/'source-manifest.json')=='a79e92b357a55434e7467950b7d9bfc30835071c30c89d7fd7f9b014232d5105'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];names=['Sign14PrefixParser','Sign14PrefixRow02'];assert len(rows)==2
for i,e in enumerate(rows):
 src=p/'src/DiophantineConsistency'/(names[i]+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and e['module']=='DiophantineConsistency.'+names[i] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports']==['DiophantineConsistency.'+('SharingSeed14Degree124' if i==0 else names[i-1])] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
s=(p/'src/DiophantineConsistency/Sign14PrefixParser.lean').read_text()
for ch,op in [('+','add'),('-','sub'),('*','mul')]:assert f"| '{ch}' => binary Expr.{op}" in s
for i,ch in enumerate('abcdefghijklmno'):assert f"| '{ch}' => some (Expr.var {i}, cs)" in s
for i,ch in enumerate('BKCF'):assert f"| '{ch}' => some (Expr.constant (p {i}), cs)" in s
for n in range(1,5):assert f"| '{n}' => some (Expr.constant {n}, cs)" in s
assert all(t in s for t in ('| 0, _ => none','| _ + 1, [] => none','| n + 1, c :: cs =>','let (left, rest) ← decode p n cs','let (right, rest) ← decode p n rest','| _ => none'))
s=(p/'src/DiophantineConsistency/Sign14PrefixRow02.lean').read_text();assert 'decode p 24 (include_str "row02.prefix").toList =' in s and 'some (SharingSeed14Degree124.row02 p, [])' in s and '  rfl' in s
f=p/'src/DiophantineConsistency/row02.prefix';g=root/'research/nine-sharing-sign14-prefix-formula/row02.prefix';assert len(f.read_bytes())==51 and sha(f)==sha(g)=='5ee89dc23b452dbc19fbc67a6c0a8ffab029ed8dab27aa8b597e6987f9648c06'
for path,pin in [('reviews/nine-sharing-sign14-staged-syntax-terminal-independent/check.py','b23e213780c74a608f7fea12b91cf1b7063c162138e2b0d430c2b788667b410d')]:q=root/path;assert sha(q)==pin;subprocess.run([sys.executable,'-I','-S','-B',str(q)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "OUT/'src/DiophantineConsistency/row02.prefix'" in r and 'final prefix drift' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':2,'scope':'51-byte embedded Nt row decoding proposal only; no all-row/JSON/PDF theorem'},indent=2))
