#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-mc-whole-bytes-retry-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='bc4fd7e7008dce24c5114e131e0da5d138c887c85df3bc4d0d99d02b83653e32' and sha(p/'source-manifest.json')=='7a5ad325359fe7422ef4100c051e550b9a8c6b2aeaf6b74eebbf9f44bb00366d'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-mc-compose-blocks-check/source-manifest.json').read_text())['rows'];assert len(rows)==21 and rows[:20]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==e['imports'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',src.read_text())
assert rows[-1]['imports']==['DiophantineConsistency.Sign17MCComposeBlocks'];s=(p/'src/DiophantineConsistency/Sign17MCWholeBytes.lean').read_text();assert all(t in s for t in ('theorem runs_eq_blocks : runs = digitBlocks.flatten ++ digitsF','noncomputable def mcBytesLE : List ℕ := byteBlocks.flatten ++ bytesF','theorem low_port_bytes : lowPort = Nat.ofDigits 256 mcBytesLE','theorem current_port2_bytes : CurrentWindowCarry2011.ports 2','exact blocks_value'))
old=root/'research/nine-sharing-sign17-mc-whole-bytes-check';oldrows=json.loads((old/'source-manifest.json').read_text())['rows'];assert rows[:20]==oldrows[:20]
oldsrc=(old/'src/DiophantineConsistency/Sign17MCWholeBytes.lean').read_text();assert oldsrc.replace('merge_replicates, Nat.reduceAdd','merge_replicates, List.replicate_append_replicate, Nat.reduceAdd')==s
oldrun=(old/'run.py').read_text();newrun=(p/'run.py').read_text();assert oldrun.replace('mc-whole-bytes-20261110','mc-whole-bytes-retry-20261110').replace('0cf514b35d053c84f4d81643c9086f9d11d630c2570186bd68cc8adb41e510d1','7a5ad325359fe7422ef4100c051e550b9a8c6b2aeaf6b74eebbf9f44bb00366d')==newrun
failure=root/'reviews/nine-sharing-sign17-mc-whole-bytes-terminal-independent/check.py';assert sha(failure)=='87932a181083b69a08b77d16361982cb928506f701ce7ef0176f090d5a029d42';subprocess.run([sys.executable,'-I','-S','-B',str(failure)],capture_output=True,check=True,timeout=120)
c=root/'reviews/nine-sharing-sign17-mc-compose-blocks-terminal-independent/check.py';assert sha(c)=='ae0002c672ac8ac062129f7cbc39ec6a64e58eb07d626ea64c7b856d77200df0';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':21,'scope':'proposed symbolic lowPort/current-port equality to compact natural byte-list decoding; no file/gzip theorem'},indent=2))
