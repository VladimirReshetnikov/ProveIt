#!/usr/bin/env python3
import ast,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-stream-explicit-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='16239e93235929439e1b1bfeebc7a68b0e19fdc4c6a0058c40fc3f98a34f31af' and sha(p/'source-manifest.json')=='cc610da0c9e0d8e46fc524a63271e92a0ab8ac17f71c1f071882a7722d0d8f87' and sha(root/'research/nine-sharing-sign17-k-stream-explicit-draft/generate.py')=='276374a35fd70158f47887d23698f280e219aa08eb7238fc01d0f93a3efff264'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign17KStreamExplicit';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();expected=['DiophantineConsistency.Sign17KCoefficientDecompose']+[f'DiophantineConsistency.Sign17KCoefficientReversed{i:02}' for i in range(8)];assert e['module']=='DiophantineConsistency.'+n and e['imports']==expected and sha(q)==sha(repo/e['source'])==e['source_sha256']=='d55310080af9ad2b0739448f22061d7a6b5accd43b5847c0147c6460837d0860' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
block=s.split('def coefficientsReversed : List ℕ := ',1)[1].split('\n\ntheorem',1)[0];chunks=[ast.literal_eval(x) for x in re.findall(r'\[[^\]]*\]',block)];assert len(chunks)==17
expected_chunks=[]
for name in ['control']+[f'block{i:02}' for i in range(15,-1,-1)]:
 j=0 if name=='control' else int(name[-2:])//2;src=(root/f'research/nine-sharing-sign17-k-coefficient-reversed-check/src/DiophantineConsistency/Sign17KCoefficientReversed{j:02}.lean').read_text();m=re.search(r'theorem '+name+r'\s*:\s*\(List\.ofFn [A-Za-z0-9_.]+\)\.reverse = (\[[^\]]*\])',src);assert m;expected_chunks.append(ast.literal_eval(m.group(1)))
assert chunks==expected_chunks;xs=sum(chunks,[]);assert len(xs)==986 and xs[984]==30099357829122 and 20+984==1004 and 'coefficientsReversed.set 984 30099357829123' in s and 'Nat.digits radix K = Sign17KRadixStream.lowPrefix' in s and s.count('#print axioms ')==3
basepaths=['nine-sharing-sign17-k-coefficient-reversed','nine-sharing-sign17-k-coefficient-decompose']
for name in basepaths:subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/(name+'-terminal-independent')/'check.py')],capture_output=True,check=True,timeout=180)
states=[json.loads((root/f'research/{name}-check/attempt01/state.json').read_text()) for name in basepaths];bases=[Path('/tmp/nine-sharing-sign17-k-coefficient-reversed-20261110'),Path('/tmp/nine-sharing-sign17-k-coefficient-decompose-20261110')];maps=[{str(Path(k).relative_to(b/'lib')):v for k,v in st['overlay_links'].items()} for st,b in zip(states,bases)];common=set(maps[0])&set(maps[1]);assert len(common)==1207 and all(maps[0][x]==maps[1][x] for x in common)
for st,b in zip(states,bases):
 for row in st['rows']:
  name=row['module'];rel='DiophantineConsistency/'+name+'.olean';target=str((b/'lib'/rel).resolve());assert rel not in maps[0] or maps[0][rel]==target;assert rel not in maps[1] or maps[1][rel]==target
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','coefficient_entries':986,'overlap':len(common),'collision_stream_index':1004,'scope':'explicit symbolic K radix digits only; fixture/file binding separate'},indent=2))
