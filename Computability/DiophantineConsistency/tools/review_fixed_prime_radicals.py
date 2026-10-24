#!/usr/bin/env python3
"""Read-only fixed-prime review; full release receipts are made in scratch."""
import argparse
import gzip
import hashlib
import importlib.util
import itertools
import json
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('review_ring', ROOT/'candidates/positive11-adaptive-shears/independent_ring.py')
ring = importlib.util.module_from_spec(spec); spec.loader.exec_module(ring)
Ring = ring.Ring

def need(ok, message):
    if not ok: raise ValueError(message)

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def focused_checks():
    c,T,R,f,Q,V,y = [Ring.variable(k) for k in ('c','T','R','f','Q','V','y')]
    need(f*c*(f*T)-f*f*R-c == f*f*(c*T-R)-c, 'old auxiliary restored exactly')
    gap=y-V
    need(V*V+(1-Q)*gap*(2*V+gap)-1 == Q*V*V-(Q-1)*y*y-1, 'gap norm restored exactly')
    t,u,k=[Ring.variable(k) for k in ('t','u','k')]
    half=2*t-(2*u+k)
    need(half*half+2*(2*u+k)*half+k*k-4 == 4*(t*t-u*(u+k)-1), 'half-first norm identity')
    L=((1,2,2),(2,1,-2),(-2,2,-1))
    need(all(sum(L[k][i]*L[k][j] for k in range(3)) == (9 if i==j else 0)
             for i in range(3) for j in range(3)), 'pentagonal lifting matrix')
    primitive=0
    for v in itertools.product(range(3), repeat=3):
        if not any(v): continue
        need(any(all(sum(L[i][j]*sgn[j]*v[j] for j in range(3))%3 for i in range(3))
                 for sgn in itertools.product((-1,1),repeat=3)), 'primitive residue lift')
        primitive+=1
    residue_cases=0
    for v,c,r,k,T,R in itertools.product(range(3),repeat=6):
        q=2;X=2;Y=(2*v+1)*q**3;a=(X+1)*Y;Delta=a*a+4*a+3
        ii=2*r+1;Df=1+Delta*ii*ii*c**4;Q=Delta*Delta*ii*ii*c**4;V=Df*(c*T-R)-c
        first=1+X*Y*Y*(X*Y*Y+1)*k*k
        need(all(z%3==1 for z in (first,Df,1+Delta*c*c,(Q*V*V-1)*pow((Q-1)%3,-1,3))), 'four base radicand units')
        residue_cases+=1
    pentagonal=0
    for N in range(1,513):
        M=24*N-21;lim=isqrt(M)//6+2
        witness=None
        for u in range(-lim,lim+1):
            for v in range(-lim,lim+1):
                S=M-(6*u-1)**2-(6*v-1)**2
                if S>=0 and isqrt(S)**2==S:
                    witness=(u,v,isqrt(S)); break
            if witness: break
        need(witness is not None, 'pentagonal positive fixture')
        pentagonal+=1
    return {'free_ring_identities':['old auxiliary','gap norm','half-centered first norm'],
            'exact_matrix_LtL':'9 I3','primitive_mod3_vectors':primitive,
            'base_radicand_mod3_cases':residue_cases,'pentagonal_positive_controls':pentagonal,
            'proof_boundary':'Finite diagnostics supplement the universal valuation and matrix-lifting proofs, not consistency tests.'}

def graph_check(p):
    available=set(p['inputs']); nodes={}
    for row in p['nodes']:
        need(row['id'] not in available and row['op'] in ('add','sub','mul') and len(row['args'])==2,'node schema')
        need(all(isinstance(a,int) or a in available for a in row['args']),'backward references')
        nodes[row['id']]=row;available.add(row['id'])
    live=set(); stack=[p['output']]
    while stack:
        a=stack.pop()
        if isinstance(a,int) or a in live: continue
        live.add(a)
        if a in nodes: stack.extend(nodes[a]['args'])
    need(set(nodes)<=live and set(p['inputs'])<=live,'whole graph and all leaves live')
    need(len(nodes)==p['live_binary_operations'],'operation count')
    return {'variables':p['variable_count'],'degree':p['exact_degree'],'operations':len(nodes),
            'all_inputs_live':True,'whole_graph_live':True,'sha256':None}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--scratch',type=Path,default=Path('/tmp/proofs62ff-fixedprime-review'))
    ap.add_argument('--output',type=Path,default=ROOT/'data/fixed-prime-radicals-review.json');args=ap.parse_args()
    arrival=json.loads((args.scratch/'ARRIVAL.json').read_text());src=args.scratch/'original/con-zfc-padic-compression'
    for r in arrival['members']: need(digest(args.scratch/'original'/r['path'])==r['sha256'],'original unchanged')
    manifest=json.loads((src/'MANIFEST.json').read_text())
    for r in manifest['files']:
        p=src/r['path'];need(digest(p)==r['sha256'] and p.stat().st_size==r['bytes'],'manifest')
    binding=json.loads((src/'coefficients/BINDING.json').read_text()); hashes={}
    for port,r in binding['ports'].items():
        raw=gzip.decompress((src/'coefficients'/r['file']).read_bytes());h=hashlib.sha256(raw).hexdigest()
        need(h==r['sha256_raw'],'fixed raw coefficient');hashes[port]=h
        need(raw==gzip.decompress((src/'forms/coefficients'/r['file']).read_bytes()),'component coefficient copy')
    need(hashes==json.loads((ROOT/'data/saturated-certificates-integer-review.json').read_text())['whole_tuple_raw_hashes'],'whole source34 tuple')
    graphs={}
    for p in sorted((src/'forms').glob('integer*.json')):
        q=json.loads(p.read_text());graphs[q['name']]=graph_check(q);graphs[q['name']]['sha256']=digest(p)
    replays={mode:json.loads((args.scratch/(mode+'-receipt.json')).read_text()) for mode in ('normal','optimized')}
    need(all(r['status']=='PASS' and len(r['equations'])==7 for r in replays.values()),'full release modes')
    need(replays['normal']['python_optimization']==0 and replays['optimized']['python_optimization']==1,'optimization propagated')
    result={'status':'PASS ordinary proof review and full finite release replays',
      'scope':'Seven unrestricted-integer equations only; inherited native theorem is explicit; no Lean or internal-model claim.',
      'arrival':{k:v for k,v in arrival.items() if k!='members'},'original_unchanged':True,
      'manifest_entries':len(manifest['files']),'whole_source34_raw_hashes':hashes,'literal_graphs':graphs,
      'focused_checks':focused_checks(),'release_replays':replays,
      'proof_assessment':['Distinct even fixed-prime valuations prevent cancellation within every squareclass, including negative classes.',
        'All five base radicands are uniformly 3-adic units; H is nonzero and divisible by3.',
        'Pentagonal square first restores N>0, then the pair guard and Q>1, then auxiliary integer descent.',
        'Canonical normalized strong and squared-modulus auxiliary witnesses are constructed explicitly.',
        'The four-root unit product needs no sign condition on the norm; the fifteen-variable strong row is enforced before denominator use.'],
      'comparison':'Thirteen-variable DAGs dominated by root fusion; fourteen-variable652/230 and664/223 trade degree for cost; fifteen-variable214/139 is a distinct degree/variable tradeoff.',
      'next_size_lead':'Replace generic expanded Taylor norm by the compact biquadratic norm, preserving the entire source polynomial.'}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','equations':len(graphs),'manifest_entries':len(manifest['files']),'files':arrival['files']}))

if __name__=='__main__': main()
