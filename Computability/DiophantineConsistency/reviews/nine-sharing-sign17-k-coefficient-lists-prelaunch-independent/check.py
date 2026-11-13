#!/usr/bin/env python3
import ast,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-coefficient-lists-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='07353491a2b9f4e139d0e9d5250fa6cf5b1200518d4a5ce933e2eaff35f4449c' and sha(p/'source-manifest.json')=='7b03edf1d716189d52c2e3557012a8f3186744db1fd93d0ec5278412018d57cd' and sha(root/'research/nine-sharing-sign17-k-coefficient-lists-draft/generate.py')=='ae530a1da98931186b03deacc4114604d979e456afb1354655d271c0ccbfac2f'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==8;seen={}
for i,e in enumerate(rows):
 n=f'Sign17KCoefficientLists{i:02}';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign17KStreamBump'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 hits=re.findall(r'theorem (block\d\d|control)\s*:\s*List\.ofFn (Sign17K(?:TileCoefficients\d\d|ControlBlocks))\.literal = (\[[^\]]*\]) := by\s*decide \+kernel',s);assert len(hits)==(3 if i==0 else 2)
 for name,ns,values in hits:
  if name=='control':assert i==0 and ns=='Sign17KControlBlocks';orig=root/'research/nine-sharing-sign17-k-control-blocks-check/src/DiophantineConsistency'/(ns+'.lean');expected=44
  else:
   k=int(name[-2:]);assert k in (2*i,2*i+1) and ns==f'Sign17KTileCoefficients{k:02}';orig=root/'research/nine-sharing-sign17-k-tile-coefficients-check/src/DiophantineConsistency'/(ns+'.lean');expected=32 if k==0 else 14 if k==15 else 64
  m=re.search(r'def literal : Fin (\d+) → ℕ := !\[(.*?)\]',orig.read_text(),re.S);assert m;v=ast.literal_eval('['+m.group(2)+']');actual=ast.literal_eval(values);assert len(v)==int(m.group(1))==expected and v==actual and name not in seen;seen[name]=len(v)
 assert s.count('#print axioms ')==len(hits)
assert len(seen)==17 and sum(v for k,v in seen.items() if k!='control')==942 and seen['control']==44
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-stream-bump-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
prior=json.loads((root/'research/nine-sharing-sign17-k-stream-bump-check/attempt01/state.json').read_text());assert prior['status']=='PASS';obj=Path('/tmp/nine-sharing-sign17-k-stream-bump-20261110/lib/DiophantineConsistency/Sign17KStreamBump.olean');assert sha(obj)==prior['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','tile_vectors':16,'tile_entries':942,'control_entries':44,'stages':8,'scope':'vector-to-list identities only; stream/fixture and file linkage separate'},indent=2))
