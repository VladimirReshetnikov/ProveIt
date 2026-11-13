#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-reflection-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='b0da947afd2e884e602548399d10920c02031ffd5553c105f252726dafcc1d8e' and sha(p/'source-manifest.json')=='4aa8c3f78a2eff585dc7acab9c380621333119a1f98bc7119e30d3dca0b7c036'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14PrefixReflection';src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14PrefixParser'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert 'def varChar (i : Fin 15) : Char := Char.ofNat (97 + i.val)' in s and [chr(97+i) for i in range(15)]==list('abcdefghijklmno')
assert "match i.val with | 0 => 'B' | 1 => 'K' | 2 => 'C' | _ => 'F'" in s
for op,ch in [('add','+'),('sub','-'),('mul','*')]:assert f"| .{op} a b => '{ch}' :: (encode a ++ encode b)" in s and f'| .{op} a b => Expr.{op} (interpret p a) (interpret p b)' in s
assert all(t in s for t in ('def depth : Code → ℕ','1 + max (depth a) (depth b)','theorem decode_encode (p : Fin 4 → ℤ) (e : Code)','∀ n : ℕ, depth e ≤ n → ∀ tail','decode p n (encode e ++ tail) = some (interpret p e, tail)'))
c=root/'reviews/nine-sharing-sign14-prefix-probe-terminal-independent/check.py';assert sha(c)=='2e9797b3f4a007068eacdb880a6d5d20a05d7760a43c7520a7ef5b31c9176206';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "['author_observed_numeric_outer_exit']==0" in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic finite prefix decode/encode/suffix theorem under sufficient depth fuel; no long row binding'},indent=2))
