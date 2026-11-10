#!/usr/bin/env python3
import gzip,hashlib,itertools,json,math,random,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier65-factor-sign-screen';source=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();rec=json.loads((pkg/'result.json').read_bytes());assert sha(source)==rec['source_sha256']=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(pkg/'screen.py')==rec['screen_sha256'] and sha(root/'research/rational-carrier64-affine-leaf-screen/screen.py')==rec['affine_engine_sha256'] and sha(root/'research/current14-carrier65-integer-leaf-superopt/screen.py')==rec['factored_engine_sha256'];g=json.loads(source.read_bytes());rows=g['source'];assert len(rows)==65
ports={}
for name,m in g['coefficient_binding']['ports'].items():
 z=(source.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];data=gzip.decompress(z);assert len(data)==m['raw_bytes'] and hashlib.sha256(data).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(data,'big')
by={r[0]:r for r in rows};factors={'N0':'product0','N1':'product0','Nt':'product3','scaled_Ns':'product4'}
for f,consumer in factors.items():assert by[f][1]=='-' and [r[0] for r in rows if f in r[2:]]==[consumer]
for row in (['product0','*','N0','N1'],['product1','*','product0','Na'],['product3','*','product1','Nt'],['product4','*','product3','scaled_Ns'],['polynomial','-','product4','Delta']):assert by[row[0]]==row
primes=tuple(rec['primes']);assert len(set(primes))==3 and all(p>1 and all(p%d for d in range(2,math.isqrt(p)+1)) for p in primes) and rec['samples_per_prime']==4 and rec['seed']==0x63A551
# For even subsets the product and output are unchanged; odd subsets negate product,
# and replacing product−Delta by product'+Delta makes output exactly −original.
for D,P in itertools.product(range(-5,6),repeat=2):assert (-P)+D==-(P-D)
sets=[v for n in range(1,5) for v in itertools.combinations(factors,n)];assert len(sets)==15 and [tuple(v['negated_factors']) for v in rec['variants']]==sets
for variant,subset in zip(rec['variants'],sets):
 A,F=variant['affine'],variant['factored'];assert A['original_live']==F['original_live']==65 and not A['candidates'] and not F['candidates'];assert all(x['counts']['unresolved_zero_scale']==x['counts']['zero_scale_skips_nonliteral']==0 for x in (A,F))
 # Independently generate exactly the 12 signatures for this variant.
 rng=random.Random(0x63A551);mods=[p for p in primes for _ in range(4)];vals={v:tuple(rng.randrange(1,p) for p in mods) for v in g['witnesses']};vals.update({name:tuple(x%p for p in mods) for name,x in ports.items()});vals.update({i:(i,)*len(mods) for i in range(5)})
 for name,op,a,b in rows:
  if name in subset:a,b=b,a
  if name=='polynomial' and len(subset)%2:op='+'
  assert name not in vals and a in vals and b in vals;nonzero=[x for x in vals if x!=0]
  for x in nonzero:
   for k in range(3):assert any(vals[x][4*k+j] for j in range(4))
  for x in nonzero:
   for y in nonzero:
    for k in range(3):assert any(vals[x][4*k+j]*vals[y][4*k+j]%primes[k] for j in range(4))
  va,vb=vals[a],vals[b];vals[name]=tuple((x+y if op=='+' else x-y if op=='-' else x*y)%p for x,y,p in zip(va,vb,mods))
for key,kind in (('affine_control','x+c'),('factor_control','(x+c)*y')):
 c=rec[key];assert c['original_live']==3 and any(x['live']==2 and x['replacement'][0]==kind for x in c['candidates'])
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-integer-leaf-superopt-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','variants':15,'scope':'even sign subsets exact output, odd subsets exact negation; bounded local one-integer-leaf rewrites only, no global minimum/Lean'},indent=2))
