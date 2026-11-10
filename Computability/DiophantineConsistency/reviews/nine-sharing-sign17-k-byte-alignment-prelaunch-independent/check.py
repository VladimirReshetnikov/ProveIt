#!/usr/bin/env python3
import ast,gzip,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-byte-alignment-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='bf182f4ddd57d34840dacb4cae1216f34dc8cc7e811e3a8207ad6763967f8626' and sha(p/'source-manifest.json')=='112ff95a9033c14c822a6872c222e0df72bd0237d569040a9739d3e170c0c7e5' and sha(root/'research/nine-sharing-sign17-k-byte-alignment-draft/generate.py')=='86544985306199665b3b7c6e55642ebb5582894e1728aaba9c3ff88befe7aea6'
seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';assert sha(seed)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';binding=json.loads(seed.read_text())['coefficient_binding'];rec=binding['ports']['K0'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();assert hashlib.sha256(packed).hexdigest()==rec['gzip_sha256'];raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()==rec['raw_sha256'] and len(raw)==11868;r=1<<47;num=int.from_bytes(raw,'big');digits=[]
while num:num,x=divmod(num,r);digits.append(x)
assert len(digits)==2021;le=raw[::-1];patterns={}
for q in (root/'research/nine-sharing-sign17-k-byte-patterns-check/src/DiophantineConsistency').glob('*.lean'):
 for label,ds,bs in re.findall(r'theorem pattern(\d+)\s*:\s*Nat.ofDigits CurrentKernel2011.radix \[([^\]]*)\]\s*=\s*Nat.ofDigits 256 \[([^\]]*)\] := by\s*decide \+kernel',q.read_text(),re.S):patterns[int(label)]=([int(x.strip()) for x in ds.split(',')],[int(x.strip()) for x in bs.split(',')])
assert set(patterns)==set(range(126));entries=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(entries)==9
for j,e in enumerate(entries):
 name='Sign17KByteAlignmentCore' if j==0 else f'Sign17KByteAlignment{j-1:02}';q=p/'src/DiophantineConsistency'/(name+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+name and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 if j==0:
  for x in ('digits.length = 8','bytes.length = 47','Nat.ofDigits CurrentKernel2011.radix digits = Nat.ofDigits 256 bytes'):assert x in s
  continue
 d=ast.literal_eval(re.search(r'^def digitBlocks : List \(List ℕ\) := (.+)$',s,re.M).group(1));b=ast.literal_eval(re.search(r'^def byteBlocks : List \(List ℕ\) := (.+)$',s,re.M).group(1));refs=re.findall(r'Sign17KBytePatterns(\d\d)\.pattern(\d\d\d)',s);lo=32*(j-1);hi=min(lo+32,252);assert len(d)==len(b)==len(refs)==hi-lo and 'List.Forall₂ Sign17KByteAlignmentCore.aligned digitBlocks byteBlocks' in s
 for k,(dl,bl,ref) in enumerate(zip(d,b,refs),lo):
  block,idx=map(int,ref);assert block==idx//16 and (dl,bl)==patterns[idx] and dl==digits[8*k:8*k+8] and bl==list(le[47*k:47*k+47])
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-byte-patterns-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
rtext=(p/'run.py').read_text();assert "need('Init' in deps" in rtext and "env['LEAN_NUM_THREADS']='1'" in rtext and "'-M3600'" in rtext and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in rtext
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':9,'full_blocks':252,'scope':'numeric fixture alignment only; tail and symbolic stream/file binding separate'},indent=2))
