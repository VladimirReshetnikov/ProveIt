#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-tile-coefficients-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='157d7ac6b48bf79a4eff04f0571b56c90795afe0cc58af9a0fa8ccfd5bc67ec9' and sha(p/'source-manifest.json')=='472d8d5e4c58dd066b0c27cd5c763023f1a2ecb69a48acede170cd8b391c1bb8'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==16
coeff=root/'research/padding-staircase-independent/coefficients.json';assert sha(coeff)=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93';v=json.loads(coeff.read_text());w=json.loads((root/'research/nine-sharing-sign17-k-ranking-witness/witness.json').read_text())['rows'];assert len(w)==942
provider=Path('/tmp/nine-sharing-sign17-k-weight-union942-20261110/src/DiophantineConsistency');covered=[]
for i,e in enumerate(rows):
 n=f'Sign17KTileCoefficients{i:02}';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();mod='Sign17KWeightAggregateProbe' if i==0 else f'Sign17KWeightAggregateBatch{i:02}';assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.'+mod] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 lo=0 if i==0 else 32+64*(i-1);hi=32 if i==0 else min(32+64*i,942);ncase=hi-lo;assert ncase==(32 if i==0 else 14 if i==15 else 64);m=re.search(r'^def literal : Fin '+str(ncase)+r' → ℕ := !\[([^]]+)\]',s,re.M);assert m;nums=[int(x) for x in m.group(1).split(',')];assert len(nums)==ncase and nums==v[lo:hi]==[2*x['weight'] for x in w[lo:hi]]
 t=(provider/(mod+'.lean')).read_text();wm=re.search(r'^def weights : Fin '+str(ncase)+r' → ℕ := !\[([^]]+)\]',t,re.M);assert wm and nums==[2*int(x) for x in wm.group(1).split(',')]
 assert f'theorem doubled_weights (i : Fin {ncase}) :' in s and f'2 * {mod}.weights i = literal i' in s;covered.extend(range(lo,hi))
assert covered==list(range(942))
for f in ('nine-sharing-sign17-k-weight-union942-terminal-independent','nine-sharing-sign17-k-ranking-witness-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':16,'cases':942,'scope':'in-Lean doubled-weight vs literal block facts, external JSON comparison Python only'},indent=2))
