#!/usr/bin/env python3
import gzip,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-byte-patterns-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='faa828e3f4b97e072d4c4cb88e0b748511c72015fcb89e552b576a0a92314986' and sha(p/'source-manifest.json')=='de91e612555bd94d074427a709bddfb8e0a718604adb8d6a7b4f167523f46797' and sha(root/'research/nine-sharing-sign17-k-byte-patterns-draft/generate.py')=='e9777d64f2d8127ab0157305ae07532765efbc39d8b0c9720ae55b939fa3496e'
seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';assert sha(seed)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';binding=json.loads(seed.read_text())['coefficient_binding'];rec=binding['ports']['K0'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();assert hashlib.sha256(packed).hexdigest()==rec['gzip_sha256'];raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()==rec['raw_sha256'] and len(raw)==11868
r=1<<47;num=int.from_bytes(raw,'big');digits=[]
while num:num,x=divmod(num,r);digits.append(x)
assert len(digits)==2021;byte=raw[::-1];allpairs=[(tuple(digits[8*i:8*i+(5 if i==252 else 8)]),tuple(byte[47*i:47*i+(24 if i==252 else 47)])) for i in range(253)];assert len(set(allpairs))==126
entries=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(entries)==8;sourcepairs=[];ids=[]
for i,e in enumerate(entries):
 name=f'Sign17KBytePatterns{i:02}';q=p/'src/DiophantineConsistency'/(name+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+name and e['imports']==['DiophantineConsistency.Sign17KRadixStreamCurrent'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 matches=re.findall(r'theorem pattern(\d+)\s*:\s*Nat.ofDigits CurrentKernel2011.radix \[([^\]]*)\]\s*=\s*Nat.ofDigits 256 \[([^\]]*)\] := by\s*decide \+kernel',s,re.S);assert len(matches)==(16 if i<7 else 14)
 for label,ds,bs in matches:
  ids.append(int(label));dl=tuple(int(x.strip()) for x in ds.split(','));bl=tuple(int(x.strip()) for x in bs.split(','));assert sum(x*r**j for j,x in enumerate(dl))==sum(x*256**j for j,x in enumerate(bl));sourcepairs.append((dl,bl))
assert ids==list(range(126)) and len(set(sourcepairs))==126 and set(sourcepairs)==set(allpairs)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-radix-stream-current-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
rtext=(p/'run.py').read_text();assert "need('Init' in deps" in rtext and "env['LEAN_NUM_THREADS']='1'" in rtext and "'-M3600'" in rtext and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in rtext
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':8,'unique_patterns':126,'external_blocks':253,'scope':'proposed numeric identities; full stream/file binding external'},indent=2))
