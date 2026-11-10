#!/usr/bin/env python3
import gzip,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-mf-compose-blocks-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='eab04cca9b6d1dd92eb80cd43341e9aeb72e13041d40e4ba12ee09fa97b3f485' and sha(p/'source-manifest.json')=='94847ee6a44de77a7bfafe91d5c5bb1e5e4b0ec8155a6045c5c524f0985f6251'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-mc-compose-core-retry-check/source-manifest.json').read_text())['rows'];mf=json.loads((root/'research/nine-sharing-sign17-mf-radix-digits-retry02-check/source-manifest.json').read_text())['rows'];chunk=json.loads((root/'research/nine-sharing-sign17-mf-chunk-check/source-manifest.json').read_text())['rows'];assert len(rows)==22 and rows[:19]==prior and rows[19]==mf[15] and rows[20]==chunk[15]
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==e['imports'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',src.read_text())
assert rows[-1]['imports']==['DiophantineConsistency.Sign17MCComposeCore','DiophantineConsistency.Sign17MFRadixDigits','DiophantineConsistency.Sign17MFChunks'];s=(p/'src/DiophantineConsistency/Sign17MFComposeBlocks.lean').read_text();seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';binding=json.loads(seed.read_text())['coefficient_binding'];rec=binding['ports']['MF'];raw=gzip.decompress((seed.parent/binding['path']/rec['file']).read_bytes());assert hashlib.sha256(raw).hexdigest()==rec['raw_sha256']=='5c15fc24e4978b878ed531abf30b2dcfe255083372034612b759b65eee1f0c25'
patterns={'A':(0,[3]+[8]*7),'B':(1,[8]*8),'C':(114,[8]*5+[0]*3),'D':(115,[0]*8),'E':(120,[1]*8),'F':(121,[1]+[0]*7),'G':(123,[0]*3+[1]*5),'H':(124,[1]*3+[0]*5),'I':(125,[0]*4+[1,2**45-4]+[0]*2),'J':(251,[0]*3+[1])}
for n,(i,digits) in patterns.items():
 bm=re.search(r'^def bytes'+n+r' : List ℕ := \[([^]]+)\]$',s,re.M);dm=re.search(r'^def digits'+n+r' : List ℕ := (.+)$',s,re.M);assert bm and dm
 bs=bytes(int(x.strip()) for x in bm[1].split(','));parts=dm[1].split(' ++ ');actual=[]
 for part in parts:
  z=re.fullmatch(r'List.replicate (\d+) (\d+)',part)
  if z:actual += [int(z[2])]*int(z[1])
  else:assert part=='[1, 2 ^ 45 - 4]';actual += [1,2**45-4]
 assert actual==digits and bs==raw[::-1][47*i:47*(i+1)] and sum(x*(1<<47)**j for j,x in enumerate(digits))==int.from_bytes(bs,'little')
assert all(t in s for t in ('[digitsA] ++ List.replicate 113 digitsB ++ [digitsC] ++ List.replicate 5 digitsD','[digitsE, digitsF, digitsD, digitsG, digitsH, digitsI] ++ List.replicate 125 digitsD','[bytesA] ++ List.replicate 113 bytesB ++ [bytesC] ++ List.replicate 5 bytesD','[bytesE, bytesF, bytesD, bytesG, bytesH, bytesI] ++ List.replicate 125 bytesD','flatten_tail blocks_aligned digitsJ bytesJ tail_value'))
for label,pin in [('mc-compose-core-retry','faaaf642fd306211ced0477f80fc46a9b6988c16ae6e4d165734d8017bebce67'),('mf-radix-digits-retry02','006ecee0b54059798e718a7d6fbaa4f5568ef8a065f7a0fc41333ca61302797d'),('mf-chunk','acebc2a89c2257a84896fabe795cee3eb1d1dd93e9093e64d0a90592d7a713b1')]:
 c=root/('reviews/nine-sharing-sign17-'+label+'-terminal-independent/check.py');assert sha(c)==pin;subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','full_blocks':251,'tail_digits':4,'scope':'proposed concrete MF block equality; no symbolic port or file binding'},indent=2))
