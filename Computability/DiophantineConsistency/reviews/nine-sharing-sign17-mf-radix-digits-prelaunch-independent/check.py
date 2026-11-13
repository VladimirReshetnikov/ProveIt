#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-mf-radix-digits-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='f8f126fbdc16d8e5bbfd44b6febe05d15b3d04f5651ccef24697a55391702462' and sha(p/'source-manifest.json')=='d468b6d74fa882fce0439f5c417a62bec5a00791d9af5ca0f34e339eff37f0fc'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==16 and rows[:15]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==e['imports'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',src.read_text())
assert rows[-1]['imports']==['DiophantineConsistency.Sign17ExactDegree'];s=(p/'src/DiophantineConsistency/Sign17MFRadixDigits.lean').read_text();assert all(t in s for t in ('def mfDigits : List ℕ := (3 :: tailDigits) ++ [1]','theorem tail_length : tailDigits.length = 2010','theorem high_port_first : highPort = 4 + radix * Nat.ofDigits radix tailDigits','theorem mf_digits_value : Nat.ofDigits radix mfDigits = highPort + beta','theorem current_port3_digits','Nat.sub_add_cancel hpos'))
tail=[8]*916+[0]*43+[1]*9+[0]*18+[1]*8+[0]*9+[1,2**45-4]+[0]*1005;assert len(tail)==2010
source=(root/'Lean/DiophantineConsistency/CurrentMaskData2011.lean').read_text();assert all(t in source for t in ('4 :: (List.replicate 916 8 ++ List.replicate 43 0 ++ List.replicate 9 1 ++','List.replicate 18 0 ++ List.replicate 8 1 ++ List.replicate 9 0 ++ [1, 2 ^ 45 - 4]','def highDigits : List ℕ := highPrefix ++ List.replicate 1005 0','def beta : ℕ := radix ^ 2011 - 1'))
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
c=root/'reviews/nine-sharing-sign17-exact-degree-terminal-independent/check.py';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','tail_digits':2010,'source_digits':2012,'scope':'proposed symbolic highPort+beta radix digits only; no byte/file theorem'},indent=2))
