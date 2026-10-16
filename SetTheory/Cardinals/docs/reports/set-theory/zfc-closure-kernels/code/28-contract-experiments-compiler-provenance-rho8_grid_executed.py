#!/usr/bin/env python3
"""Systematically price safe rho8 permutations on the source19 full logic.

This experiment changes no theory, quantifier row, equality row or arithmetic
codec. It retains source19's selected equivalent C/G conjunction layout. The
streamed rho8 variable is read once. Costs include the actual dispatch depth.
The imported source19 and upstream files are never changed.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import cache
import hashlib
import importlib
import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys
import time

HERE = Path(__file__).resolve().parent
SOURCE = HERE/'incoming/zfc_substitution_engine/zfc_substitution_engine/engineering'
REPO = SOURCE/'vendor/proveit'
RESEARCH = REPO/'Computability/BusyBeaver/Research/ZFC'
PRIOR = SOURCE/'vendor/one_schema_machine'
sys.path[:0] = [str(RESEARCH), str(PRIOR), str(SOURCE)]
import full_logic_search as s
import theory_backend_experiment as t
import recover_wade_dag as r
import rebracket_axioms as g
from audit_raw_candidate import normalize_named


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True)+'\n')


def safe_repair(word, seed, exponent):
    """Same overlap correction as ProveIt b90a825, with exact disjoint counts."""
    rng, seq, rules = random.Random(seed), list(word), []
    while True:
        counts = Counter(zip(seq, seq[1:]))
        for pair in list(counts):
            if pair[0] == pair[1]:
                i = count = 0
                while i + 1 < len(seq):
                    if (seq[i],seq[i+1]) == pair:
                        count += 1; i += 2
                    else:
                        i += 1
                counts[pair] = count
        choices = [(p,n) for p,n in counts.items() if n >= 2]
        if not choices:
            return seq, rules
        pair = rng.choices([p for p,_ in choices], [n**exponent for _,n in choices])[0]
        new, i = [], 0
        while i < len(seq):
            if i + 1 < len(seq) and (seq[i],seq[i+1]) == pair:
                new.append(300+len(rules)); i += 2
            else:
                new.append(seq[i]); i += 1
        assert len(seq)-len(new) >= 2
        rules.append(pair); seq = new


def coarsen(word):
    out, i = [], 0
    while i < len(word):
        if word[i:i+2] == [166,119]:
            out.append(161); i += 2
        else:
            out.append(word[i]); i += 1
    return out


def expand_grammar(seq, rules):
    known = {}
    for i,(a,b) in enumerate(rules):
        known[300+i] = known.get(a,[a]) + known.get(b,[b])
    return [x for q in seq for x in known.get(q,[q])]


def measure(nodes):
    @cache
    def zeros(q):
        edge = nodes[q][0]
        return 1 + zeros(int(edge[6:])) if edge.startswith('ENode ') else 1
    depth = max(2,max(zeros(q) for q in nodes))
    return len(nodes)+55+depth, depth


def builder_dag(builder, backend):
    reachable=set(builder.reachable()); root=builder.find_seq('main().0')
    order=[root]+sorted(reachable-{root}); ids={q:i for i,q in enumerate(order)}
    def edge(x):
        if isinstance(x,int): return f'ENode {ids[x]}'
        if x=='halt': return 'EHalt'
        if x.startswith('_'):
            return ('EBreak ' if x.startswith('_break.') else 'EContinue ')+x.rsplit('.',1)[1]
        _,reg,op=x.split('.')
        return ('EInc ' if op=='inc' else 'EDecnz ')+str(r.REGISTERS.index(reg))
    return ({ids[q]:tuple(edge(x) for x in builder.sequences[q].seq) for q in order},
            {ids[q]:builder.sequences[q].name for q in order})


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--seeds',type=int,default=2048)
    ap.add_argument('--start-seed',type=int,default=0)
    ap.add_argument('--exponents',type=int,nargs='+',default=[4,8])
    ap.add_argument('--modes',nargs='+',choices=['legacy','safe'],default=['legacy','safe'])
    ap.add_argument('--perms',type=int,nargs='+',default=list(range(12)))
    args=ap.parse_args()
    assert __debug__ and args.seeds>0 and args.start_seed>=0
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    nodes,names=r.parse_dag(r.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    old_contract=t.old_contract(nodes)
    spec,specsha=t.published_spec()
    rows=spec['ax_rows']('a','h','b','c','u')
    perms=[dict(zip(('a','b','c','u'),p)) for p in itertools.permutations(('a','b','c','u'))
           if p[0]!='u' and p[2]!='u']
    assert len(perms)==12
    C=s.variants(spec['bundle_C']('a','b','c'),t)
    G=s.variants(spec['bundle_G']('a','b','c'),t)
    V=[t.Imp(rel('a','b'),t.All('c',rel('a','b'))) for rel in (t.Rel,t.Eq)]
    orders=list(itertools.permutations(range(4)))
    components=[C[2],G[1],*V]
    bundle=s.trees([components[i] for i in orders[16]],t)[1]
    words={}
    asts={}
    for i,p in enumerate(perms):
        fs=[s.rename(rows[1],p),*[rows[j] for j in range(2,9)]]
        assert t.emit(fs[0]).count(158)==1
        word=[166,121,180,176]+[m for f in fs for m in t.emit(f)]+t.emit(bundle)+t.TAIL
        actual,_=t.symbolic(word)
        assert actual==['old_top',t.All('a','h'),*fs,bundle]
        assert all(g.bounder(nodes)(f'ENode {q}')==(0,0) for q in set(word))
        words[i]=coarsen(word);asts[i]=(word,fs)
    backendpath=REPO/'lib/jeff-busy-beaver-zfc254/ZF/generator'
    sys.path.insert(0,str(backendpath));backend=importlib.import_module('TMBuilder')
    start=time.monotonic();cases=0;best=None;hist={};improvements=[];compiled=0
    def candidate(pi,mode,exp,seed):
        seq,rules=(g.repair if mode=='legacy' else safe_repair)(words[pi],seed,exp)
        nn,nm,ax=g.transform(nodes,names,seq,rules)
        cost,depth=measure(nn)
        return dict(perm=pi,mode=mode,exponent=exp,seed=seed,working_states=cost,
                    decisions=len(nn),dispatch_depth=depth,nodes=nn,names=nm,
                    root=ax,seq=seq,rules=rules)
    def summary(x):
        return {k:x[k] for k in ('perm','mode','exponent','seed','working_states','decisions','dispatch_depth')}
    def verify_compile(x):
        nonlocal compiled
        machine=g.compile_dag(backend,x['nodes'],x['names'])
        g.reextract(machine,x['nodes'],x['names'])
        states={q for q,_ in machine.states}
        framework={q for q in states if q[0].isdigit()}
        assert len(states)==x['working_states'],(summary(x),len(states))
        assert len(framework)==55+x['dispatch_depth'],(summary(x),len(framework))
        compiled+=1
        return machine
    baseline=candidate(0,'legacy',4,341)
    assert baseline['working_states']==268
    verify_compile(baseline)
    best=baseline;improvements.append(dict(case=0,**summary(best)))
    def checkpoint():
        write_json(out/'search-progress.json',dict(cases=cases,best=summary(best),
                  histograms=hist,improvements=improvements,compiled=compiled,
                  elapsed_seconds=time.monotonic()-start))
        write_json(out/'best-recipe.json',dict(**summary(best),parameter_permutation=perms[best['perm']]))
    checkpoint()
    for pi,exp,mode in itertools.product(args.perms,args.exponents,args.modes):
        h=Counter();depths=Counter()
        for seed in range(args.start_seed,args.start_seed+args.seeds):
            x=candidate(pi,mode,exp,seed);cases+=1
            h[x['working_states']]+=1;depths[x['dispatch_depth']]+=1
            key=(x['working_states'],x['decisions'],len(x['rules']),len(x['seq']))
            bkey=(best['working_states'],best['decisions'],len(best['rules']),len(best['seq']))
            if key<bkey:
                verify_compile(x)
                if x['working_states']<best['working_states']:
                    improvements.append(dict(case=cases,**summary(x)))
                    print(json.dumps(improvements[-1]),flush=True)
                best=x;checkpoint()
        hist[f'{pi}/{exp}/{mode}']=dict(states=dict(h),dispatch_depth=dict(depths))
        checkpoint()
        print(json.dumps(dict(cases=cases,lane=[pi,exp,mode],best=summary(best),elapsed=time.monotonic()-start)),flush=True)
    machine=verify_compile(best)
    assert expand_grammar(best['seq'],best['rules'])==words[best['perm']]
    named=out/'candidate.named.tm';machine.save(str(named))
    numeric,labels,meta=normalize_named(named.read_bytes())
    (out/'candidate.tm').write_bytes(numeric)
    write_json(out/'labels.json',labels)
    write_json(out/'candidate.dag.json',dict(root=0,nodes=best['nodes'],names=best['names'],axioms_root=best['root']))
    word,fs=asts[best['perm']]
    builder=r.builder_from_dag(backend,nodes,names)
    builder.sequence_lookup={ss.seq:i for i,ss in enumerate(builder.sequences)}
    t.lower_program(builder,nodes,word,'rho8_systematic_reference',shared=True)
    ref,refnames=builder_dag(builder,backend)
    cert,stats=g.bisimulation(ref,best['nodes'])
    write_json(out/'reference.dag.json',dict(root=0,nodes=ref,names=refnames))
    write_json(out/'rm_certificate.json',cert)
    write_json(out/'grammar.json',dict(word=words[best['perm']],seq=best['seq'],rules=best['rules']))
    write_json(out/'source_semantics.json',dict(rho8_parameter_permutation=perms[best['perm']],logical_rows=fs,
              theory_bundle=bundle,expanded_word=word,stream_u_occurrences=t.emit(fs[0]).count(158)))
    checkpoint()
    result=dict(pin='4747142d5d15213eb711bdadfa3cc7e769fcb7a7',source19_arrival='be9e617d28ce0032213c27b59c3039c0495e6b83',
                upstream_pin=r.COMMIT,args=dict(seeds=args.seeds,start_seed=args.start_seed,exponents=args.exponents,modes=args.modes,perms=args.perms),
                cases=cases,best=summary(best),compiled_candidates=compiled,source_reference_nodes=len(ref),
                literal_table=meta,sha256=hashlib.sha256(numeric).hexdigest(),rm_certificate=stats,
                improved268=best['working_states']<268,binary_simulation_proved=False,
                internal_ZFC_endpoint_proved=False,elapsed_seconds=time.monotonic()-start,
                driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),spec_sha256=specsha)
    write_json(out/'results.json',result)
    print(json.dumps(result),flush=True)


if __name__=='__main__':main()
