#!/usr/bin/env python3
"""Measure PSC while retaining all original equality-bearing logical rows.

Keeps the original base-four relative-falsity codec. All controls include both
atomic equality and membership vacuity. These are costs, not calibrated new
machines. The lack of a primitive false / ordinary-logic transfer theorem is
explicitly retained as an obligation. Written artifacts stay under --output.
"""
from __future__ import annotations
import argparse, hashlib, importlib, itertools, json, sys
from collections import Counter
from pathlib import Path

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--prior',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--seeds',type=int,default=512)
    args=ap.parse_args()
    repo=args.repo.resolve();out=args.output.resolve();prior=args.prior.resolve()
    assert out!=repo and repo not in out.parents
    out.mkdir(parents=True,exist_ok=True)
    sys.path[:0]=[str(repo/'Computability/BusyBeaver/Research/ZFC'),str(prior)]
    import recover_wade_dag as r
    import theory_backend_experiment as t
    import psc_backend_experiment as psc
    import rebracket_axioms as g
    from audit_raw_candidate import normalize_named
    nodes,names=r.parse_dag(r.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    nodes[219]=('EInc 1','EInc 1');names[219]='two_top_increments'
    spec,specsha=t.published_spec();rows=spec['ax_rows']('a','h','b','c','u')
    prefix=[166,121,180,176]+[m for f in rows[1:] for m in t.emit(f)]
    vr=t.Imp(t.Rel('a','b'),t.All('c',t.Rel('a','b')))
    ve=t.Imp(t.Eq('a','b'),t.All('c',t.Eq('a','b')))
    vac=t.And(vr,ve)
    phi=psc.psc_template()
    free=t.Imp(phi[1],phi[2][2])
    ir=t.All(1,t.Not(t.Rel(1,1)))
    def emit(f):
        word=psc.emit(f);out=[];i=0
        while i<len(word):
            if word[i:i+2]==[psc.INC,psc.INC]:out.append(219);i+=2
            else:out.append(word[i]);i+=1
        return out
    def coarse(word):
        out=[];i=0
        while i<len(word):
            if word[i:i+2]==[166,119]:out.append(161);i+=2
            else:out.append(word[i]);i+=1
        return out
    recipes={'full_PSC':prefix+emit(phi)+t.emit(vac)+t.TAIL,
             'free_root_PSC':prefix+emit(free)+t.emit(vac)+t.TAIL,
             'full_PSC_IR':prefix+emit(phi)+t.emit(ir)+t.emit(vac)+t.TAIL,
             'free_root_PSC_IR':prefix+emit(free)+t.emit(ir)+t.emit(vac)+t.TAIL}
    backenddir=out/'backend';backenddir.mkdir(exist_ok=True)
    for fn in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):
        (backenddir/fn).write_bytes(r.git_bytes(None,'ZF/generator/'+fn))
    sys.path.insert(0,str(backenddir));backend=importlib.import_module('TMBuilder')
    results={}
    for label,word in recipes.items():
        assert all(g.bounder(nodes)(f'ENode {q}')==(0,0) for q in set(word))
        best=1000;dist=Counter();winner=None;bestnodes=None
        for seed,alpha in itertools.product(range(args.seeds),(1,2,4,8)):
            seq,gr=g.repair(coarse(word),seed,alpha)
            nn,nm,ax=g.transform(nodes,names,seq,gr)
            cost=len(nn)+62;dist[cost]+=1
            if cost<best:
                best=cost;winner=(seed,alpha);bestnodes=(nn,nm,ax,len(seq),len(gr))
        nn,nm,ax,reslen,ng=bestnodes
        machine=g.compile_dag(backend,nn,nm);g.reextract(machine,nn,nm)
        path=out/(label+'.named.tm');machine.save(str(path))
        numeric,labels,meta=normalize_named(path.read_bytes())
        assert meta['working_states']==best
        (out/(label+'.tm')).write_bytes(numeric)
        (out/(label+'.dag.json')).write_text(json.dumps({'root':0,'nodes':nn,'names':nm},indent=2)+'\n')
        results[label]={'minimum_working_states':best,'grammar_seed':winner[0],
            'grammar_alpha':winner[1],'search_cases':sum(dist.values()),
            'cost_distribution':dict(sorted(dist.items())),
            'logical_rows_retained':list(range(8,0,-1)),
            'membership_and_equality_vacuity_retained':True,
            'macro_word':word,'grammar_productions':ng,'residual_length':reslen,
            'table':meta,'calibration_and_binary_compiler_proved':False}
        print(json.dumps({'variant':label,'minimum':best,'recipe':winner}),flush=True)
    result={'source_pin':'47f3a3602946dfe48803a91a910c646e74637ac8',
            'upstream_pin':r.COMMIT,'spec_sha256':specsha,
            'formula_codec':'original Imp4P/Rel4P+1/All4P+2/Eq4P+3, F=Rel(0,0)',
            'fixed_logical_row_order':True,'searched_family_not_minimality':True,
            'primitive_false_calculus_claimed':False,'new_ZFC_bound_claimed':False,
            'results':results,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (out/'full_logic_psc_results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')

if __name__=='__main__':main()
