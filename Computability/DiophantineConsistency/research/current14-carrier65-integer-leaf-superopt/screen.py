#!/usr/bin/env python3
"""Current-port one-new-integer-leaf modular rewrite screen; no Lean."""
import ast
import gzip
import hashlib
import json
from pathlib import Path
import random
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent;D=HERE.parents[1]
ENGINE=D/'research/rational-carrier64-affine-leaf-screen/screen.py'
SOURCE=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
ENGINE_HASH='4a11bfec6db2a1cee0d87f71c02fe7cd04f27385001e906cf84616c05201f2fe'
GRAPH_HASH='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
PRIMES=(1_000_000_007,1_000_000_009,998_244_353);SAMPLES=4;SEED=0x63A551
def sha(data):return hashlib.sha256(data).hexdigest()
def need(condition,message):
    if not condition:raise RuntimeError(message)
def read(path,pin):
    data=path.read_bytes();need(sha(data)==pin,f'pin mismatch: {path}');return data
def live(rows,output):
    # Fixed leaves and inputs are free; count reachable binary gates only.
    edges={r[0]:r[2:] for r in rows};seen=set();todo=[output]
    while todo:
        node=todo.pop()
        if node in edges and node not in seen:
            seen.add(node);todo.extend(edges[node])
    return len(seen)
engine=ast.parse(read(ENGINE,ENGINE_HASH),filename=str(ENGINE))
defs=[x for x in engine.body if isinstance(x,ast.FunctionDef) and x.name=='samples_for']
need(len(defs)==1,'engine function missing')
exec(compile(ast.Module(body=defs,type_ignores=[]),str(ENGINE),'exec'))
for p in PRIMES:
    need(p>1 and all(p%d for d in range(2,int(p**0.5)+1)),'modulus is not prime')
g=json.loads(read(SOURCE,GRAPH_HASH));rows=g['source'];output=g['output']
need(len(rows)==65 and live(rows,output)==65 and len(g['witnesses'])==14,'unexpected source graph')
ports={}
for name,meta in g['coefficient_binding']['ports'].items():
    packed=(SOURCE.parent/'coefficients'/meta['file']).read_bytes()
    need(sha(packed)==meta['gzip_sha256'],'compressed port mismatch')
    data=gzip.decompress(packed);need(sha(data)==meta['raw_sha256'],'raw port mismatch')
    ports[name]=int.from_bytes(data,'big')
affine=samples_for(rows,g['witnesses'],ports,output)
control=samples_for([['a','+','x',1],['t','+','a',2],['out','*','t','y']],['x','y'],{},'out')
need(any(x['target']=='t' and x['live']==2 for x in control['candidates']),'affine positive control failed')
need(affine['counts']['unresolved_zero_scale']==0 and affine['counts']['zero_scale_skips_nonliteral']==0,
     'sample has an unresolved scale')

def factored_search(rows,variables,constants,output):
    rng=random.Random(SEED);mods=[p for p in PRIMES for _ in range(SAMPLES)]
    values={v:tuple(rng.randrange(1,p) for p in mods) for v in variables}
    values.update({v:tuple(n%p for p in mods) for v,n in constants.items()})
    values.update({i:(i,)*len(mods) for i in range(5)})
    counts={'targets':0,'factor_queries':0,'product_offset_queries':0,'scaled_product_queries':0,
            'zero_scale_skips_nonliteral':0,'unresolved_zero_scale':0,'raw_survivors':0}
    candidates=[];original=live(rows,output)
    def save(index,name,first,second,kind,x,y,residues):
        counts['raw_survivors']+=1
        changed=rows[:index]+[['__fresh__',*first],[name,*second]]+rows[index+1:]
        size=live(changed,output)
        if size<original:
            candidates.append({'target':name,'replacement':[kind,x,y],
                               'new_coefficient_mod_primes':residues,'live':size})
    for index,(name,op,a,b) in enumerate(rows):
        need(name not in values and a in values and b in values,'invalid topological row')
        aa,bb=values[a],values[b]
        target=tuple((x+y if op=='+' else x-y if op=='-' else x*y)%p
                     for x,y,p in zip(aa,bb,mods))
        earlier=list(values)
        for y in earlier:
            vy=values[y]
            # For x*y+c, c must be constant across all witness samples.
            for x in earlier:
                vx=values[x]
                product=tuple(a*b%p for a,b,p in zip(vx,vy,mods))
                numer=tuple((a-b)%p for a,b,p in zip(target,product,mods))
                residues=[numer[k*SAMPLES] for k in range(len(PRIMES))]
                counts['product_offset_queries']+=1
                if all(numer[k*SAMPLES+j]==residues[k] for k in range(len(PRIMES)) for j in range(SAMPLES)):
                    save(index,name,['*',x,y],['+','__fresh__','__new_leaf__'],'x*y+c',x,y,residues)
                if not all(z==0 for z in product):
                    pivots=[]
                    for k,p in enumerate(PRIMES):
                        start=k*SAMPLES;j=next((j for j in range(start,start+SAMPLES) if product[j]),None)
                        if j is None:
                            counts['unresolved_zero_scale']+=1;break
                        pivots.append((p,j,pow(product[j],-1,p)))
                    if len(pivots)==len(PRIMES):
                        counts['scaled_product_queries']+=1;rr=[];ok=True
                        for k,(p,j,inv) in enumerate(pivots):
                            c=target[j]*inv%p;start=k*SAMPLES
                            if any((target[z]-c*product[z])%p for z in range(start,start+SAMPLES)):
                                ok=False;break
                            rr.append(c)
                        if ok:
                            save(index,name,['*',x,y],['*','__fresh__','__new_leaf__'],'c*(x*y)',x,y,rr)
                elif x!=0 and y!=0:
                    counts['zero_scale_skips_nonliteral']+=1
            if all(z==0 for z in vy):
                if y!=0:counts['zero_scale_skips_nonliteral']+=1
                continue
            pivots=[]
            for k,p in enumerate(PRIMES):
                start=k*SAMPLES;j=next((j for j in range(start,start+SAMPLES) if vy[j]),None)
                if j is None:
                    counts['unresolved_zero_scale']+=1;break
                pivots.append((p,j,pow(vy[j],-1,p)))
            if len(pivots)!=len(PRIMES):continue
            # (x+c)*y and (c-x)*y; c is inferred independently per prime.
            for x in earlier:
                vx=values[x]
                for sign,kind in ((1,'(x+c)*y'),(-1,'(c-x)*y')):
                    counts['factor_queries']+=1
                    numer=tuple((a-sign*b*c)%p for a,b,c,p in zip(target,vx,vy,mods))
                    residues=[];ok=True
                    for k,(p,j,inv) in enumerate(pivots):
                        c=numer[j]*inv%p;start=k*SAMPLES
                        if any((numer[z]-c*vy[z])%p for z in range(start,start+SAMPLES)):
                            ok=False;break
                        residues.append(c)
                    if ok:
                        first=['+',x,'__new_leaf__'] if sign==1 else ['-','__new_leaf__',x]
                        save(index,name,first,['*','__fresh__',y],kind,x,y,residues)
        values[name]=target;counts['targets']+=1
    return {'original_live':original,'candidates':candidates,'counts':counts}

factored=factored_search(rows,g['witnesses'],ports,output)
fcontrol=factored_search([['a','+','x',1],['b','+','a',2],['out','*','b','y']],['x','y'],{},'out')
need(any(x['target']=='out' and x['live']==2 for x in fcontrol['candidates']),'factor positive control failed')
need(factored['counts']['unresolved_zero_scale']==0 and factored['counts']['zero_scale_skips_nonliteral']==0,
     'sample has an unresolved factored scale')
print(json.dumps({'source_sha256':GRAPH_HASH,'engine_sha256':ENGINE_HASH,
 'screen_sha256':sha(Path(__file__).read_bytes()),'primes':PRIMES,'samples_per_prime':SAMPLES,'seed':SEED,
 'affine':affine,'factored':factored,'affine_control':control,'factor_control':fcontrol,
 'scope':'current ports; one new arbitrary integer leaf, enumerated local forms only'},sort_keys=True,indent=2))
