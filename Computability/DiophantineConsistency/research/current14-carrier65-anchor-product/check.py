#!/usr/bin/env python3
"""Build two anchor-product variants and screen affine target rewrites, no Lean."""
import ast,gzip,hashlib,json,random,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site: raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw);rows=g['source'];variables=g['witnesses'];output=g['output']
ports={}
for name,meta in g['coefficient_binding']['ports'].items():
 z=(p.parent/'coefficients'/meta['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==meta['gzip_sha256']
 b=gzip.decompress(z);assert hashlib.sha256(b).hexdigest()==meta['raw_sha256'];ports[name]=int.from_bytes(b,'big')
engine=D/'research/rational-carrier64-affine-leaf-screen/screen.py'; eraw=engine.read_bytes()
assert hashlib.sha256(eraw).hexdigest()=='4a11bfec6db2a1cee0d87f71c02fe7cd04f27385001e906cf84616c05201f2fe'
PRIMES=(1_000_000_007,1_000_000_009,998_244_353);SAMPLES=4;SEED=0x63A551
def need(ok,msg):
 if not ok: raise RuntimeError(msg)
expr=ast.parse(eraw);functions=[x for x in expr.body if isinstance(x,ast.FunctionDef) and x.name in ('live','samples_for')]
assert len(functions)==2
exec(compile(ast.Module(body=functions,type_ignores=[]),str(engine),'exec'))
assert rows[33]==['R','+','rproduct','mask'] and rows[45][0]=='Nt'
variants={}
for anchor in ('N1','Nt'):
 if anchor=='N1': prefix=rows[:34];tail=rows[34:]
 else: prefix=rows[:34]+rows[41:46];tail=rows[34:41]+rows[46:]
 new=prefix+[['rank_anchor','*','R',anchor]]+[[r[0],r[1],*['rank_anchor' if x=='R' else x for x in r[2:]]] for r in tail]
 assert live(new,output)==66
 available=set(variables)|set(ports)|set(range(5))
 for name,op,a,b in new:
  assert name not in available and a in available and b in available
  available.add(name)
 result=samples_for(new,variables,ports,output)
 assert result['counts']['unresolved_zero_scale']==0 and result['counts']['zero_scale_skips_nonliteral']==0
 variants[anchor]=result
 print(anchor,'complete',file=sys.stderr,flush=True)
control=samples_for([['a','+','x',1],['t','+','a',2],['out','*','t','y']],['x','y'],{},'out')
assert any(x['target']=='t' and x['live']==2 for x in control['candidates'])
print(json.dumps({'control':control,'variants':variants,'goal_below_65':{a:[v for v in r['candidates'] if v['live']<65] for a,r in variants.items()},'primes':PRIMES,'samples':SAMPLES,'seed':SEED,'scope':'single-target affine modular screen after one-multiply anchored rank shear; filters only'},sort_keys=True,indent=2))
