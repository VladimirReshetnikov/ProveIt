#!/usr/bin/env python3
"""Factor sign variants, then bounded one-leaf local rewrites."""
import ast
import gzip
import hashlib
import itertools
import json
from pathlib import Path
import random
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent;D=HERE.parents[1]
SOURCE=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
AFFINE=D/'research/rational-carrier64-affine-leaf-screen/screen.py'
FACTORED=D/'research/current14-carrier65-integer-leaf-superopt/screen.py'
pins={SOURCE:'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e',
 AFFINE:'4a11bfec6db2a1cee0d87f71c02fe7cd04f27385001e906cf84616c05201f2fe',
 FACTORED:'798f0bf746be8fd2a53b5060d4955be8689c4b79e6eb1a6969f710a8ce299b0a'}
def sha(data):return hashlib.sha256(data).hexdigest()
def need(ok,reason):
    if not ok:raise RuntimeError(reason)
for p,h in pins.items():need(sha(p.read_bytes())==h,f'pin mismatch: {p}')
PRIMES=(1_000_000_007,1_000_000_009,998_244_353);SAMPLES=4;SEED=0x63A551
def live(rows,output):
    edges={r[0]:r[2:] for r in rows};seen=set();todo=[output]
    while todo:
        x=todo.pop()
        if x in edges and x not in seen:seen.add(x);todo.extend(edges[x])
    return len(seen)
for path,name in ((AFFINE,'samples_for'),(FACTORED,'factored_search')):
    tree=ast.parse(path.read_bytes(),filename=str(path))
    defs=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name==name]
    need(len(defs)==1,'screen function missing')
    exec(compile(ast.Module(body=defs,type_ignores=[]),str(path),'exec'))
for p in PRIMES:
    need(p>1 and all(p%d for d in range(2,int(p**0.5)+1)),'sample modulus not prime')
control_rows=[['a','+','x',1],['b','+','a',2],['out','*','b','y']]
affine_control=samples_for(control_rows,['x','y'],{},'out')
factor_control=factored_search(control_rows,['x','y'],{},'out')
need(any(x['target']=='b' and x['live']==2 for x in affine_control['candidates']),
     'affine positive control failed')
need(any(x['target']=='out' and x['live']==2 for x in factor_control['candidates']),
     'factored positive control failed')
g=json.loads(SOURCE.read_bytes());rows=g['source'];output=g['output'];ports={}
need(len(rows)==65 and live(rows,output)==65,'unexpected graph')
for name,m in g['coefficient_binding']['ports'].items():
    packed=(SOURCE.parent/'coefficients'/m['file']).read_bytes()
    need(sha(packed)==m['gzip_sha256'],'gzip hash mismatch')
    raw=gzip.decompress(packed);need(sha(raw)==m['raw_sha256'],'raw hash mismatch')
    ports[name]=int.from_bytes(raw,'big')
factors={'N0':'product0','N1':'product0','Nt':'product3','scaled_Ns':'product4'}
for factor,consumer in factors.items():
    row=next(r for r in rows if r[0]==factor)
    need(row[1]=='-' and [r[0] for r in rows if factor in r[2:]]==[consumer],
         f'unexpected factor use: {factor}')
expected={'product0':['product0','*','N0','N1'],
          'product1':['product1','*','product0','Na'],
          'product3':['product3','*','product1','Nt'],
          'product4':['product4','*','product3','scaled_Ns'],
          'polynomial':['polynomial','-','product4','Delta']}
for name,row in expected.items():need(next(r for r in rows if r[0]==name)==row,'product chain drift')
def evaluate(graph,values,mod):
    env=dict(values)
    for n,op,a,b in graph:
        x=env[a] if isinstance(a,str) else a;y=env[b] if isinstance(b,str) else b
        env[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()%mod
    return env[output]
results=[];rng=random.Random(0x5A17)
subsets=[v for size in range(1,len(factors)+1) for v in itertools.combinations(factors,size)]
for pair in subsets:
    variant=[r[:] for r in rows]
    for row in variant:
        if row[0] in pair:row[2],row[3]=row[3],row[2]
        if row[0]=='polynomial' and len(pair)%2:row[1]='+'
    for _ in range(30):
        values={name:rng.randrange(1,1000) for name in g['witnesses']+g['fixed_numerals']}
        before=evaluate(rows,values,PRIMES[0]);after=evaluate(variant,values,PRIMES[0])
        need(after==((-before if len(pair)%2 else before)%PRIMES[0]),'sign control failed')
    affine=samples_for(variant,g['witnesses'],ports,output)
    factored=factored_search(variant,g['witnesses'],ports,output)
    for result in (affine,factored):
        need(result['counts']['unresolved_zero_scale']==0 and result['counts']['zero_scale_skips_nonliteral']==0,
             'unresolved zero scale')
    results.append({'negated_factors':pair,'affine':affine,'factored':factored})
print(json.dumps({'source_sha256':pins[SOURCE],'affine_engine_sha256':pins[AFFINE],
 'factored_engine_sha256':pins[FACTORED],'screen_sha256':sha(Path(__file__).read_bytes()),
 'primes':PRIMES,'samples_per_prime':SAMPLES,'seed':SEED,
 'sign_identity':'factor-sign subset; odd subsets negate the entire output',
 'modular_sign_controls_per_variant':30,'affine_control':affine_control,
 'factor_control':factor_control,'variants':results},sort_keys=True,indent=2))
