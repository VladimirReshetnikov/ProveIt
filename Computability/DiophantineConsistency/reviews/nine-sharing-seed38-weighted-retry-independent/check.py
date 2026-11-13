#!/usr/bin/env python3
"""Independent source/delta and retained failure review; does not invoke Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];root=next(p for p in D.parents if (p/'lakefile.toml').is_file());O=D/'research/nine-sharing-seed38-split-draft';N=D/'research/nine-sharing-seed38-weighted-retry';T=Path('/tmp/nine-sharing-seed38-split-20261105');BASE=Path('/tmp/nine-fresh-jones-client-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,s):
 if not x:raise RuntimeError(s)
need(sha(N/'run.py')=='8e1b2963e8dc9f9a406f3bea29ba3cae24fab3cb06e7a16ca3e8e11fe0dbf999' and sha(N/'source-manifest.json')=='9c00d40c96d65f202b76e5fd378ebdf14a9345dd555949e1382395599183420c','retry pins')
need(sha(O/'run.py')=='17dda5818da1a84875d6213cf2b0a080ffce99585294231524199b905998cc0c' and sha(O/'source-manifest.json')=='c4ce5fd28170206e920d1f2f755d995225c40c1eef53d1a0a1d8c76020af03fa','predecessor pins')
a=(O/'run.py').read_text().replace('/tmp/nine-sharing-seed38-split-20261105','/tmp/nine-sharing-seed38-weighted-retry-20261105').replace('c4ce5fd28170206e920d1f2f755d995225c40c1eef53d1a0a1d8c76020af03fa','9c00d40c96d65f202b76e5fd378ebdf14a9345dd555949e1382395599183420c');need(a==(N/'run.py').read_text(),'runner delta')
x=json.loads((O/'source-manifest.json').read_text())['rows'];y=json.loads((N/'source-manifest.json').read_text())['rows'];need(len(x)==len(y)==10 and len({e['module'] for e in y})==10,'manifest uniqueness')
old=(O/'src/DiophantineConsistency/SharingSeed38Weighted.lean').read_text();new=(N/'src/DiophantineConsistency/SharingSeed38Weighted.lean').read_text();extra='''/-- Constructor-oriented rewrites for the overloaded syntax operations. -/\nprivate theorem degree_add (w : Fin 39 → ℕ) (a b : Expr (Fin 39)) :\n    (a + b).weightedDegree w = max (a.weightedDegree w) (b.weightedDegree w) := rfl\nprivate theorem degree_sub (w : Fin 39 → ℕ) (a b : Expr (Fin 39)) :\n    (a - b).weightedDegree w = max (a.weightedDegree w) (b.weightedDegree w) := rfl\nprivate theorem degree_mul (w : Fin 39 → ℕ) (a b : Expr (Fin 39)) :\n    (a * b).weightedDegree w = a.weightedDegree w + b.weightedDegree w := rfl\n\n'''
need(new==old.replace('/-- Candidate syntax-degree calculation;',extra+'/-- Candidate syntax-degree calculation;').replace('    Expr.weightedDegree]','    degree_add, degree_sub, degree_mul, Expr.weightedDegree]'),'source delta');need(sha(N/'src/DiophantineConsistency/SharingSeed38Weighted.lean')=='40fe8bdb068458736ddf9e4c6e0fa7b476ad52ad5e422ab157f41916d4176b7d','weighted source pin')
seen=set();mods={e['module'] for e in y}
for i,(a,b) in enumerate(zip(x,y)):
 if i!=4:need(a==b,'unexpected manifest change')
 else:need({k:v for k,v in a.items() if k not in ('source','source_sha256')}=={k:v for k,v in b.items() if k not in ('source','source_sha256')},'weighted manifest')
 f=root/b['source'];need(sha(f)==b['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',f.read_text(),re.M)==b['imports'],'source/import '+b['module'])
 for dep in b['imports']:
  if dep in mods:need(dep in seen,'topological dependency '+dep)
 need(not os.path.lexists(BASE/'lib'/Path(*b['module'].split('.')).with_suffix('.olean')),'base shadow '+b['module']);seen.add(b['module'])
need(y[4]['module']=='DiophantineConsistency.SharingSeed38Weighted','weighted position')
p=O/'attempt01/state.json';need(sha(p)==sha(T/'state.json')=='b1dc0d908a26bfdc3a657a29ae9cb7b98a3d6b10e560a04e5b245903b4057814','state pin');s=json.loads(p.read_bytes());need(s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed SharingSeed38Weighted')" and len(s['rows'])==5,'failure state')
for path,target in s['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'overlay '+path)
for i,r in enumerate(s['rows']):
 name=r['module'];need(name==x[i]['module'].split('.')[-1] and sha(T/'src/DiophantineConsistency'/(name+'.lean'))==r['source_sha256']==x[i]['source_sha256'],'old stage source '+name)
 for kind in ('deps','compile'):
  v=r[kind];need(v['exit']==(1 if i==4 and kind=='compile' else 0) and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'],'exit '+name+kind)
  need(sha(T/(name+'-'+kind+'.txt'))==sha(O/'attempt01'/(name+'-'+kind+'.txt'))==v['log_sha256'],'log '+name+kind)
 for path,v in r['direct_guard'].items():
  f=Path(path)
  if v is None:need(not os.path.lexists(f),'guard absence '+path)
  else:need(f.is_file() and str(f.resolve())==v['realpath'] and sha(f)==v['sha256'],'guard '+path)
 if i<4:need(sha(T/'lib/DiophantineConsistency'/(name+'.olean'))==r['object_sha256'],'stage object '+name)
 else:need(not r.get('object_sha256') and 'error: unsolved goals' in (T/(name+'-compile.txt')).read_text(),'weighted failed diagnostic')
q=subprocess.run([sys.executable,'-I','-S','-B',str(N/'run.py'),'--preflight'],capture_output=True,text=True,timeout=60);need(q.returncode==0 and json.loads(q.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT','independent preflight '+q.stderr)
print(json.dumps({'status':'PASS_SCOPED_PRELAUNCH_REVIEW','prior_passing_stages':4,'prior_failed_weighted_stage':True,'overlay_links':len(s['overlay_links']),'direct_guard_slots':sum(len(r['direct_guard']) for r in s['rows']),'preflight_exit':q.returncode,'scope':'Source/runner deltas and retained observations only; no Lean compilation or proof of retry.'},indent=2,sort_keys=True))
