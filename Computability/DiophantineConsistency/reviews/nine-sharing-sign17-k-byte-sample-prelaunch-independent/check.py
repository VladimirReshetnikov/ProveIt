#!/usr/bin/env python3
import gzip,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-byte-sample-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='264b0281e5f73c9d78969fc4b3433f6ea246ccfd3e1309e52771aa2b0386e669' and sha(p/'source-manifest.json')=='ae3a35aeaadda9590bab26f986b696896501a22733a423759f8cfaaabc5853b6' and sha(root/'research/nine-sharing-sign17-k-byte-sample-draft/generate.py')=='59b4b5bd7268b919bfd017b447ec2c87c471e11d2be736b592dfae1b15dea387'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign17KByteSample.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign17KByteSample' and e['imports']==['DiophantineConsistency.Sign17KRadixStreamCurrent'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='1e21afdfbdab096bb503174c0125be6355200dea6a1890186e01e33a6e68f712' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';assert sha(seed)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';binding=json.loads(seed.read_text())['coefficient_binding'];rec=binding['ports']['K0'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();assert hashlib.sha256(packed).hexdigest()==rec['gzip_sha256'];raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()==rec['raw_sha256'] and len(raw)==11868
r=1<<47;num=int.from_bytes(raw,'big');digits=[]
while num:num,x=divmod(num,r);digits.append(x)
assert len(digits)==2021;byte=raw[::-1];matches=re.findall(r'theorem block(\d+)\s*:\s*Nat.ofDigits CurrentKernel2011.radix \[([^\]]*)\]\s*=\s*Nat.ofDigits 256 \[([^\]]*)\] := by\s*decide \+kernel',s,re.S);assert [int(x[0]) for x in matches]==[2,125,126,252]
for label,ds,bs in matches:
 i=int(label);dl=[int(x.strip()) for x in ds.split(',')];bl=[int(x.strip()) for x in bs.split(',')];assert dl==digits[8*i:8*i+(5 if i==252 else 8)] and bl==list(byte[47*i:47*i+(24 if i==252 else 47)]) and sum(x*r**j for j,x in enumerate(dl))==sum(x*256**j for j,x in enumerate(bl))
assert digits[1004]==30099357829123
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-radix-stream-current-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
rtext=(p/'run.py').read_text();assert "need('Init' in deps" in rtext and "env['LEAN_NUM_THREADS']='1'" in rtext and "'-M3600'" in rtext and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in rtext
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','blocks':[2,125,126,252],'scope':'four proposed numeric block identities, snapshot comparison external; no full stream/file theorem'},indent=2))
