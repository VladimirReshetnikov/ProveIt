#!/usr/bin/env python3
"""Bounded modular filter for one new fixed rational leaf; no Lean invoked."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')

import gzip
import hashlib
import json
import random
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
GRAPH = ROOT/'research/rational-carrier64-independent/polynomial.json'
COEFF = ROOT/'candidates/one-page-reversed-carrier65-2521/coefficients'
GRAPH_HASH = '8fd205a43c4045914d88f4117ba263cf7a232ac26c64dcf09a1c37a8d88e7b27'
PRIMES = (1_000_000_007, 1_000_000_009, 998_244_353)
SAMPLES = 4
SEED = 0x63A551

def need(ok, reason):
    if not ok:
        raise RuntimeError(reason)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def live(rows, output):
    edges = {r[0]:r[2:] for r in rows}
    seen, todo = set(), [output]
    while todo:
        node = todo.pop()
        if node in edges and node not in seen:
            seen.add(node)
            todo.extend(edges[node])
    return len(seen)

def samples_for(rows, variables, constants, output):
    rng = random.Random(SEED)
    modulus = [p for p in PRIMES for _ in range(SAMPLES)]
    values = {v:tuple(rng.randrange(1,p) for p in modulus) for v in variables}
    values.update({v:tuple(x % p for p in modulus) for v,x in constants.items()})
    for literal in range(5):
        values[literal] = (literal,)*len(modulus)
    original = live(rows, output)
    all_candidates = []
    counts = {'targets':0, 'one_affine_queries':0, 'two_affine_queries':0,
              'unresolved_zero_scale':0, 'zero_scale_skips_nonliteral':0,
              'constant_queries':0, 'alias_queries':0, 'raw_survivors':0}
    def scale_ok(numer, denom, pivots):
        residues = []
        for k,(p,j,inv) in enumerate(pivots):
            start = k*SAMPLES
            c = numer[j] * inv % p
            if any((numer[i]-c*denom[i]) % p for i in range(start,start+SAMPLES)):
                return False
            residues.append(c)
        return residues
    for i,(name,op,a,b) in enumerate(rows):
        need(name not in values and a in values and b in values, 'invalid topological graph')
        va,vb = values[a],values[b]
        if op == '+': t=tuple((x+y)%p for x,y,p in zip(va,vb,modulus))
        elif op == '-': t=tuple((x-y)%p for x,y,p in zip(va,vb,modulus))
        elif op == '*': t=tuple(x*y%p for x,y,p in zip(va,vb,modulus))
        else: raise RuntimeError('invalid graph operation')
        earlier = list(values)
        def save(replacement, desc, residues):
            counts['raw_survivors'] += 1
            changed=rows[:i]+replacement+rows[i+1:]
            size=live(changed,output)
            if size<original:
                all_candidates.append({'target':name,'replacement':desc,
                                       'new_coefficient_mod_primes':residues,'live':size})
        # A row replaced directly by the fresh leaf, or an earlier node,
        # costs no arithmetic operation. Rewrite all downstream references.
        def alias_save(replacement, desc, residues):
            changed=[list(row) for row in rows if row[0] != name]
            for row in changed:
                row[2:] = [replacement if z == name else z for z in row[2:]]
            new_output = replacement if output == name else output
            size=live(changed,new_output)
            if size < original:
                all_candidates.append({'target':name,'replacement':desc,
                                       'new_coefficient_mod_primes':residues,'live':size})
        counts['constant_queries'] += 1
        residue=[t[k*SAMPLES] for k in range(len(PRIMES))]
        if all(t[k*SAMPLES+j]==residue[k] for k in range(len(PRIMES)) for j in range(SAMPLES)):
            alias_save('__new_leaf__',['c'],residue)
        for x in earlier:
            vx=values[x]
            counts['alias_queries'] += 1
            if t == vx:
                alias_save(x,['alias',x],None)
            # One binary operation with a new constant: x+c, c-x, c*x.
            for sign,label in ((1,'x+c'),(-1,'c-x')):
                counts['one_affine_queries'] += 1
                r=tuple((tv-sign*xv)%p for tv,xv,p in zip(t,vx,modulus))
                residues=[r[k*SAMPLES] for k in range(len(PRIMES))]
                if all(r[k*SAMPLES+j]==residues[k] for k in range(len(PRIMES)) for j in range(SAMPLES)):
                    row=[name,'+',x,'__new_leaf__'] if sign==1 else [name,'-','__new_leaf__',x]
                    save([row],[label,x],residues)
            # A zero scale produces only 0, already covered by the offset
            # tests above; it cannot determine the new coefficient.
            if all(z == 0 for z in vx):
                if x != 0:
                    counts['zero_scale_skips_nonliteral'] += 1
                continue
            pivots=[]
            for k,p in enumerate(PRIMES):
                start=k*SAMPLES
                j=next((j for j in range(start,start+SAMPLES) if vx[j]),None)
                if j is None:
                    counts['unresolved_zero_scale'] += 1
                    break
                pivots.append((p,j,pow(vx[j],-1,p)))
            if len(pivots) != len(PRIMES):
                continue
            counts['one_affine_queries'] += 1
            c=scale_ok(t,vx,pivots)
            if c is not False and c is not None:
                save([[name,'*','__new_leaf__',x]],['c*x',x],c)
            # Two operations, c*x +/- y, with exactly one fresh gate.
            for y in earlier:
                vy=values[y]
                for sign,label in ((1,'c*x+y'),(-1,'c*x-y')):
                    counts['two_affine_queries'] += 1
                    numer=tuple((tv-sign*yv)%p for tv,yv,p in zip(t,vy,modulus))
                    c=scale_ok(numer,vx,pivots)
                    if c is not False and c is not None:
                        save([['__fresh__','*','__new_leaf__',x],
                              [name,'+' if sign==1 else '-','__fresh__',y]],
                             [label,x,y],c)
        values[name]=t
        counts['targets']+=1
    return {'original_live':original,'candidates':all_candidates,'counts':counts}

def main():
    for p in PRIMES:
        need(p > 1 and all(p % d for d in range(2, int(p**0.5)+1)), 'sample modulus not prime')
    raw=GRAPH.read_bytes()
    need(sha(raw)==GRAPH_HASH, 'source graph hash changed')
    graph=json.loads(raw)
    need(len(graph['source'])==64 and live(graph['source'],graph['output'])==64, 'wrong graph')
    ports={}
    for port, meta in graph['coefficient_binding']['ports'].items():
        compressed=(COEFF/meta['file']).read_bytes()
        need(sha(compressed)==meta['gzip_sha256'], port+' compressed hash')
        data=gzip.decompress(compressed)
        need(sha(data)==meta['raw_sha256'] and len(data)==meta['raw_bytes'], port+' raw hash')
        ports[port]=int.from_bytes(data,'big')
    # Fixed-port values are evaluated modulo each prime, preserving the
    # denominator in Urank rather than silently treating it as integral.
    # Interpolate via CRT only for initial leaves; candidate coefficients
    # remain independent residues and require subsequent exact proof.
    modulus=1
    for p in PRIMES: modulus*=p
    need(all(ports['beta']%p for p in PRIMES), 'sample prime divides beta')
    urank=ports['MF']*pow(ports['beta'],-1,modulus)%modulus
    constants={'beta':ports['beta'],'K0':ports['K0'],'Urank':urank,'Wrank':ports['MC']-ports['MF']}
    result=samples_for(graph['source'],graph['witnesses'],constants,graph['output'])
    control=samples_for([['a','+','x',1],['t','+','a',2],['out','*','t','y']],['x','y'],{},'out')
    need(any(x['target']=='t' and x['live']==2 for x in control['candidates']), 'positive control failed')
    need(result['counts']['unresolved_zero_scale']==0, 'sample has unresolved zero denominator')
    need(result['counts']['zero_scale_skips_nonliteral']==0, 'nonliteral sampled identically zero')
    print(json.dumps({'graph_sha256':GRAPH_HASH,'screen_sha256':sha(Path(__file__).read_bytes()),
        'primes':PRIMES,'samples_per_prime':SAMPLES,'seed':SEED,
        'coefficient_port_gzip_hashes':{k:v['gzip_sha256'] for k,v in graph['coefficient_binding']['ports'].items()},
        'screen':result,'positive_control':control},indent=2,sort_keys=True))

if __name__ == '__main__':
    main()
