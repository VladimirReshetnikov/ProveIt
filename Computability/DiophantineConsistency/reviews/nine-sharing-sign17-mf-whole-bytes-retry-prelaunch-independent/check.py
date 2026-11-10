#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-mf-whole-bytes-retry-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='4241b9bccc3feafcdf7e628ee5fe5f0b3dd979e837b208c3c9607b335ad0a826' and sha(p/'source-manifest.json')=='5b1d5e34e1fb2edd2f88e894b527eaeb1823bca254365fd1a291c1aab8c1ac55'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-mf-compose-blocks-check/source-manifest.json').read_text())['rows'];assert len(rows)==23 and rows[:22]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==e['imports'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',src.read_text())
assert rows[-1]['imports']==['DiophantineConsistency.Sign17MFComposeBlocks'];s=(p/'src/DiophantineConsistency/Sign17MFWholeBytes.lean').read_text();assert all(t in s for t in ('theorem digits_eq_blocks : mfDigits = digitBlocks.flatten ++ digitsJ','noncomputable def mfBytesLE : List ℕ := byteBlocks.flatten ++ bytesJ','theorem mf_port_bytes : highPort + beta = Nat.ofDigits 256 mfBytesLE','theorem current_port3_bytes : CurrentWindowCarry2011.ports 3','exact blocks_value'))
old=root/'research/nine-sharing-sign17-mf-whole-bytes-check';oldrows=json.loads((old/'source-manifest.json').read_text())['rows'];assert rows[:22]==oldrows[:22]
oldsrc=(old/'src/DiophantineConsistency/Sign17MFWholeBytes.lean').read_text();assert oldsrc.replace('List.append_nil, List.append_assoc, merge_replicates','List.append_nil, List.cons_append, List.append_assoc, merge_replicates')==s
oldrun=(old/'run.py').read_text();newrun=(p/'run.py').read_text();assert oldrun.replace('mf-whole-bytes-20261110','mf-whole-bytes-retry-20261110').replace('078058a4a9e4a096d393a105bf37b9614e8335ec640c84f80723cdc5dafcf2ed','5b1d5e34e1fb2edd2f88e894b527eaeb1823bca254365fd1a291c1aab8c1ac55')==newrun
failure=root/'reviews/nine-sharing-sign17-mf-whole-bytes-terminal-independent/check.py';assert sha(failure)=='477a1b9924fd8fd47e84ae35ca722a17063bdbae4499e3d94d6d97874a05529a';subprocess.run([sys.executable,'-I','-S','-B',str(failure)],capture_output=True,check=True,timeout=120)
c=root/'reviews/nine-sharing-sign17-mf-compose-blocks-terminal-independent/check.py';assert sha(c)=='674cfa5237040adfe2c9e325b76cee45dde3d3c233a0d0895ee1ee5305dbb95e';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':23,'scope':'proposed symbolic highPort+beta/current-port3 equality to compact natural byte-list decoding; no file/gzip theorem'},indent=2))
