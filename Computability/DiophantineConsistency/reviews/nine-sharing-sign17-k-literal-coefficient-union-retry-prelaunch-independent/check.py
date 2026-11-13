#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-literal-coefficient-union-retry-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='a5dc940d319e5b0f11c52ca04a4eda6e0de08ba82c962ec85583ba15d22de6cd' and sha(p/'source-manifest.json')=='9b013ec6321bfafa59e6f44b0ab0ec85fd65b2add95b1249f5499a5c00d6caf5' and sha(root/'research/nine-sharing-sign17-k-tile-coefficient-union-draft/generate.py')=='68b3dbb6e571b7c9937dc1d9f7e555a822446e98ed6903caabd0a68378373ab8'
for name in ('nine-sharing-sign17-k-tile-coefficients-terminal-independent','nine-sharing-sign17-k-full-coefficients-blocks-terminal-independent','nine-sharing-sign17-k-weight-union942-terminal-independent','nine-sharing-sign17-k-literal-coefficient-union-failure-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/name/'check.py')],capture_output=True,check=True,timeout=180)
entries=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(entries)==9
sizes=[96,224,352,480,608,736,864,942];lengths=[32]+[64]*14+[14];assert sum(lengths)==942
for ix,size in enumerate(sizes):
 e=entries[ix];name=f'Sign17KTileCoeffUnion{size}';q=p/'src/DiophantineConsistency'/(name+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+name and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 assert f'def literal : Fin {size} → ℕ' in s and f'theorem doubled_weights (i : Fin {size})' in s and f'Sign17KWeightUnion{size}.weights i = literal i' in s
 if ix==0:
  assert 'Sign17KTileCoefficients00.literal Sign17KTileCoefficients01.literal' in s and 'Sign17KWeightAggregateProbe.weights Sign17KWeightAggregateBatch01.weights' in s
 else:
  prev=sizes[ix-1];mid=prev+64;i=2*ix
  for x in (f'def literal{mid} : Fin {mid}',f'Sign17KTileCoeffUnion{prev}.literal Sign17KTileCoefficients{i:02}.literal',f'def literal : Fin {size} → ℕ := Fin.append literal{mid}',f'Sign17KTileCoefficients{i+1:02}.literal',f'Sign17KWeightUnion{prev}.weights Sign17KWeightAggregateBatch{i:02}.weights',f'Sign17KWeightUnion{size}.weights{mid} Sign17KWeightAggregateBatch{i+1:02}.weights',f'Sign17KTileCoefficients{i:02}.doubled_weights',f'Sign17KTileCoefficients{i+1:02}.doubled_weights') :assert x in s,(name,x)
  assert prev==sum(lengths[:i]) and mid==sum(lengths[:i+1]) and size==sum(lengths[:i+2])
e=entries[8];q=p/'src/DiophantineConsistency/Sign17KLiteralCoefficients.lean';s=q.read_text();assert sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for x in ('Fin 986 → ℕ := Fin.append','Sign17KTileCoeffUnion942.literal Sign17KControlBlocks.literal','Sign17KFullCoefficients.coefficients i = literal i','r ^ 18 + r ^ 1004 + r ^ 2020','literal i * r ^ (1005 - i.val)','theorem K_literal'):assert x in s
old=root/'research/nine-sharing-sign17-k-literal-coefficient-union-check/src/DiophantineConsistency'
for entry in entries[:8]:
 name=entry['module'].split('.')[-1];assert (old/(name+'.lean')).read_bytes()==(p/'src/DiophantineConsistency'/(name+'.lean')).read_bytes()
a=(old/'Sign17KLiteralCoefficients.lean').read_text();new=(p/'src/DiophantineConsistency/Sign17KLiteralCoefficients.lean').read_text();start='theorem rawWord_literal (r : ℕ) :';end='\ntheorem K_literal :';assert a.split(start)[0]==new.split(start)[0] and a.split(end)[1]==new.split(end)[1];a0=a.split(start)[1].split(end)[0];n0=new.split(start)[1].split(end)[0];assert a0.split(':= by')[0]==n0.split(':= by')[0] and 'congr 1' in a0 and 'have hsum :' in n0 and 'Finset.sum_congr rfl' in n0 and 'congrArg (fun z : ℕ =>' in n0
run=(p/'run.py').read_text();assert "env['LEAN_NUM_THREADS']='1'" in run and "need('Init' in deps" in run and "'-M3600'" in run and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in run
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);v=json.loads(x.stdout);assert not x.stderr and v['status']=='PASS_NO_LEAN_PREFLIGHT' and v['stage_count']==9
print(json.dumps({'status':'PASS_PRELAUNCH','stages':9,'block_lengths':lengths,'tile_total':sum(lengths),'scope':'source-only proof retry for in-Lean literal coefficient union; no external JSON/file/PDF theorem; survey not complete transitive trace'},indent=2))
