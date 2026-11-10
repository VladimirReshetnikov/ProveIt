#!/usr/bin/env python3
import gzip,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-mc-compose-blocks-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='0b079d41b8736c3c01fcda5b35085df7a49c949574096640d55c8f365580fe46' and sha(p/'source-manifest.json')=='73805ededa7e05423f51fbe872c5d1e5de6fab373b4e2c3f8888e2e1552d1d05'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-mc-compose-core-retry-check/source-manifest.json').read_text())['rows'];assert len(rows)==20 and rows[:19]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==e['imports'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',src.read_text())
assert rows[-1]['imports']==['DiophantineConsistency.Sign17MCComposeCore'];s=(p/'src/DiophantineConsistency/Sign17MCComposeBlocks.lean').read_text();seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';binding=json.loads(seed.read_text())['coefficient_binding'];rec=binding['ports']['MC'];raw=gzip.decompress((seed.parent/binding['path']/rec['file']).read_bytes());assert hashlib.sha256(raw).hexdigest()==rec['raw_sha256']=='2b5c9296e32616260e64a051c92892645b9aa1bf0bf4c0d931e464080702ca9f'
patterns={'A':(0,[2]*8),'B':(118,[2]*7+[1]),'C':(119,[1]*8),'D':(123,[2]*2+[1]*6),'E':(125,[1]*4+[2]+[1]*3),'F':(251,[1]*3)}
for n,(i,offsets) in patterns.items():
 bm=re.search(r'^def bytes'+n+r' : List ℕ := \[([^]]+)\]$',s,re.M);dm=re.search(r'^def digits'+n+r' : List ℕ := (.+)$',s,re.M);assert bm and dm
 bs=bytes(int(x.strip()) for x in bm[1].split(','));runs=re.findall(r'List.replicate (\d+) \(radix - (\d+)\)',dm[1]);assert [int(v) for count,v in runs for _ in range(int(count))]==offsets and bs==raw[::-1][47*i:47*(i+1)] and sum(((1<<47)-v)*((1<<47)**j) for j,v in enumerate(offsets))==int.from_bytes(bs,'little')
assert all(t in s for t in ('List.replicate 118 digitsA ++ [digitsB, digitsC] ++ List.replicate 3 digitsA','[digitsD, digitsC, digitsE] ++ List.replicate 125 digitsC','List.replicate 118 bytesA ++ [bytesB, bytesC] ++ List.replicate 3 bytesA','[bytesD, bytesC, bytesE] ++ List.replicate 125 bytesC','flatten_tail blocks_aligned digitsF bytesF tail_value'))
c=root/'reviews/nine-sharing-sign17-mc-compose-core-retry-terminal-independent/check.py';assert sha(c)=='faaaf642fd306211ced0477f80fc46a9b6988c16ae6e4d165734d8017bebce67';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','full_blocks':251,'tail_digits':3,'scope':'proposed concrete block value equality, not yet symbolic lowPort or file binding'},indent=2))
