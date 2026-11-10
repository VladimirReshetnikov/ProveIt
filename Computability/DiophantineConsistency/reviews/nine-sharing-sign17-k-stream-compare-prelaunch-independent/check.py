#!/usr/bin/env python3
import ast,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-stream-compare-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='52f8da8eaeea136ed50e660f5838422c52e28bd144b2e9f75b018b68626674a6' and sha(p/'source-manifest.json')=='c4a30962977cc7d4cc873cd7eb45143f2d567b5785fd1ced4f81e7ef3ca8f9cb'
entries=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(entries)==8;imports=['DiophantineConsistency.Sign17KStreamExplicit','DiophantineConsistency.Sign17KByteCompose']
for i,e in enumerate(entries):
 n=f'Sign17KStreamCompare{i:02}';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==imports and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==imports and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 assert f'coefficientsReversed.set 984 30099357829123' in s and f')).drop {i*256}).take 256' in s and f'(Sign17KByteCompose.digitList.drop {i*256}).take 256' in s and 'decide +kernel' in s and s.count('#print axioms ')==1
s=(root/'research/nine-sharing-sign17-k-stream-explicit-check/src/DiophantineConsistency/Sign17KStreamExplicit.lean').read_text();segment=s.split('def coefficientsReversed : List ℕ := ',1)[1].split('\n\ntheorem',1)[0];actual=sum([ast.literal_eval(x) for x in re.findall(r'\[[^\]]*\]',segment)],[]);assert len(actual)==986 and actual[984]==30099357829122;actual[984]+=1;actual=[0]*18+[1,0]+actual+[0]*1014+[1]
fixture=[]
for i in range(8):
 t=(root/f'research/nine-sharing-sign17-k-byte-alignment-check/src/DiophantineConsistency/Sign17KByteAlignment{i:02}.lean').read_text();m=re.search(r'def digitBlocks : List \(List ℕ\) := (\[.*\])',t);assert m;blocks=ast.literal_eval(m.group(1));assert all(len(x)==8 for x in blocks);fixture.extend(sum(blocks,[]))
fixture += [0,0,0,0,1];assert len(actual)==len(fixture)==2021 and actual==fixture and [len(actual[i:i+256]) for i in range(0,2021,256)]==[256]*7+[229]
basepaths=['nine-sharing-sign17-k-stream-explicit','nine-sharing-sign17-k-byte-compose-retry'];bases=[Path('/tmp/nine-sharing-sign17-k-stream-explicit-20261110'),Path('/tmp/nine-sharing-sign17-k-byte-compose-retry-20261110')]
for name in basepaths:subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/(name+'-terminal-independent')/'check.py')],capture_output=True,check=True,timeout=180)
states=[json.loads((root/f'research/{name}-check/attempt01/state.json').read_text()) for name in basepaths];maps=[{str(Path(k).relative_to(b/'lib')):v for k,v in st['overlay_links'].items()} for st,b in zip(states,bases)];common=set(maps[0])&set(maps[1]);assert len(common)==1188 and all(maps[0][x]==maps[1][x] for x in common)
for st,b in zip(states,bases):
 for row in st['rows']:
  rel='DiophantineConsistency/'+row['module']+'.olean';target=str((b/'lib'/rel).resolve());assert rel not in maps[0] or maps[0][rel]==target;assert rel not in maps[1] or maps[1][rel]==target
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':8,'python_list_length':2021,'last_chunk_length':229,'provider_overlap':len(common),'scope':'proposed eight bounded in-Lean digit comparisons only; full-list assembly and external-file theorem separate'},indent=2))
