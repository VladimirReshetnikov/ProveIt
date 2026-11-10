#!/usr/bin/env python3
import gzip,hashlib,json,math,random,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier65-integer-leaf-superopt';source=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';engine=root/'research/rational-carrier64-affine-leaf-screen/screen.py';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();rec=json.loads((pkg/'result.json').read_bytes());assert sha(source)==rec['source_sha256']=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(engine)==rec['engine_sha256']=='4a11bfec6db2a1cee0d87f71c02fe7cd04f27385001e906cf84616c05201f2fe' and sha(pkg/'screen.py')==rec['screen_sha256'];g=json.loads(source.read_bytes());rows=g['source'];assert len(rows)==65 and len(g['witnesses'])==14
# Exact fixed port payloads, in the integer-leaf graph.
ports={}
for name,m in g['coefficient_binding']['ports'].items():
 z=(source.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];data=gzip.decompress(z);assert len(data)==m['raw_bytes'] and hashlib.sha256(data).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(data,'big')
primes=tuple(rec['primes']);assert len(set(primes))==3 and all(p>1 and all(p%d for d in range(2,math.isqrt(p)+1)) for p in primes) and rec['samples_per_prime']==4 and rec['seed']==0x63A551
# Count live binary gates only; constants and inputs are leaves.
deps={n:(a,b) for n,_,a,b in rows};seen=set();stack=[g['output']]
while stack:
 x=stack.pop()
 if x in deps and x not in seen:seen.add(x);stack.extend(deps[x])
assert len(seen)==65
rng=random.Random(0x63A551);mods=[p for p in primes for _ in range(4)];vals={v:tuple(rng.randrange(1,p) for p in mods) for v in g['witnesses']};vals.update({name:tuple(x%p for p in mods) for name,x in ports.items()});vals.update({i:(i,)*len(mods) for i in range(5)})
for i,(name,op,a,b) in enumerate(rows):
 assert name not in vals and a in vals and b in vals
 # Every potentially nonliteral denominator has a nonzero pivot for every prime.
 earlier=list(vals);nonzero=[x for x in earlier if x!=0]
 for x in nonzero:
  for k in range(3):assert any(vals[x][4*k+j] for j in range(4))
 # c*(x*y) needs at least one simultaneous nonzero product in each prime.
 for x in nonzero:
  for y in nonzero:
   for k in range(3):assert any(vals[x][4*k+j]*vals[y][4*k+j]%primes[k] for j in range(4))
 va,vb=vals[a],vals[b];vals[name]=tuple((x+y if op=='+' else x-y if op=='-' else x*y)%p for x,y,p in zip(va,vb,mods))
assert len(vals)==14+4+5+65
A=rec['affine'];F=rec['factored'];assert A['original_live']==F['original_live']==65 and not A['candidates'] and not F['candidates'];ac=A['counts'];fc=F['counts'];assert ac['targets']==fc['targets']==65 and ac['alias_queries']==sum(23+i for i in range(65))==3575 and ac['constant_queries']==65 and ac['one_affine_queries']==sum(3*(23+i)-1 for i in range(65))==10660 and ac['two_affine_queries']==fc['factor_queries']==sum(2*(23+i)*(22+i) for i in range(65))==431860 and fc['product_offset_queries']==sum((23+i)**2 for i in range(65))==219505 and fc['scaled_product_queries']==sum((22+i)**2 for i in range(65))==212420 and ac['raw_survivors']==116 and fc['raw_survivors']==342
assert all(d['counts']['unresolved_zero_scale']==d['counts']['zero_scale_skips_nonliteral']==0 for d in (A,F))
for key,kind in (('affine_control','x+c'),('factor_control','(x+c)*y')):
 c=rec[key];assert c['original_live']==3 and any(x['live']==2 and x['replacement'][0]==kind and x['new_coefficient_mod_primes']==[3,3,3] for x in c['candidates'])
# Distinct prime residues are necessary for any fixed integer c and are always CRT-compatible.
assert all(math.gcd(x,y)==1 for i,x in enumerate(primes) for y in primes[i+1:])
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-dag-expression-retry-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'actual payload-port, exact-target one-new-integer-leaf families; no global-minimum/zero-only/Lean claim'},indent=2))
