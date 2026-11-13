#!/usr/bin/env python3
import gzip,hashlib,json,math,random,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier65-anchor-product';source=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';engine=root/'research/rational-carrier64-affine-leaf-screen/screen.py';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(source)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(engine)=='4a11bfec6db2a1cee0d87f71c02fe7cd04f27385001e906cf84616c05201f2fe' and sha(pkg/'check.py')=='43ae10117147ebbe389d6abebb5389f1f1d760b5ffad5674e5eb529f884cd593' and sha(pkg/'result.json')=='b82f43951a82ca01621802ec7dfefd32b7709a344e31d54581962868f35a3c81';g=json.loads(source.read_bytes());rows=g['source'];rec=json.loads((pkg/'result.json').read_text());assert len(rows)==65 and len(g['witnesses'])==14
ports={}
for name,m in g['coefficient_binding']['ports'].items():
 z=(source.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];data=gzip.decompress(z);assert len(data)==m['raw_bytes'] and hashlib.sha256(data).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(data,'big')
P=tuple(rec['primes']);assert len(set(P))==3 and all(p>1 and all(p%d for d in range(2,math.isqrt(p)+1)) for p in P) and rec['samples']==4 and rec['seed']==0x63A551
for anchor in ('N1','Nt'):
 prefix=rows[:34] if anchor=='N1' else rows[:34]+rows[41:46];tail=rows[34:] if anchor=='N1' else rows[34:41]+rows[46:];new=prefix+[['rank_anchor','*','R',anchor]]+[[r[0],r[1]]+['rank_anchor' if x=='R' else x for x in r[2:]] for r in tail];assert len(new)==66
 deps={r[0]:r[2:] for r in new};live=set();todo=[g['output']]
 while todo:
  x=todo.pop()
  if x in deps and x not in live:live.add(x);todo.extend(deps[x])
 assert len(live)==66
 rng=random.Random(0x63A551);mods=[p for p in P for _ in range(4)];vals={x:tuple(rng.randrange(1,p) for p in mods) for x in g['witnesses']};vals.update({name:tuple(x%p for p in mods) for name,x in ports.items()});vals.update({i:(i,)*len(mods) for i in range(5)})
 for name,op,a,b in new:
  assert name not in vals and a in vals and b in vals
  for x in vals:
   if x!=0:
    for k in range(3):assert any(vals[x][4*k+j] for j in range(4))
  va,vb=vals[a],vals[b];vals[name]=tuple((x+y if op=='+' else x-y if op=='-' else x*y)%p for x,y,p in zip(va,vb,mods))
 v=rec['variants'][anchor];c=v['counts'];assert v['original_live']==66 and not v['candidates'] and not rec['goal_below_65'][anchor] and c['targets']==66 and c['alias_queries']==sum(23+i for i in range(66))==3663 and c['one_affine_queries']==sum(3*(23+i)-1 for i in range(66))==10923 and c['two_affine_queries']==sum(2*(23+i)*(22+i) for i in range(66))==447172 and c['unresolved_zero_scale']==c['zero_scale_skips_nonliteral']==0
ctl=rec['control'];assert ctl['original_live']==3 and any(x['target']=='t' and x['live']==2 and x['replacement']==['x+c','x'] for x in ctl['candidates'])
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-multiplicative-shear-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'two 66-gate anchored shears, bounded exact-target affine screen with one arbitrary integer leaf; no global minimum or Lean theorem'},indent=2))
