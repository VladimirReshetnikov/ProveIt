#!/usr/bin/env python3
"""Reproduce two complete-table compiler controls against pinned ProveIt sources.

Usage:
  python compiler_controls.py --repo /path/to/ProveIt \
    --prior-grammar /path/to/rebracket_axioms.py --output /tmp/compiler-controls

Original control: exactly the published219-node program, reassociated to207
decision nodes by the previously supplied seed341/exponent4 method (269 total).
PSC control: every original logical row, fresh-offset PSC, separate IR, and
gated membership/equality vacuity, measured at283 total in this bounded family.

Neither generated table has a newly verified complete binary simulation here.
The PSC control additionally needs an emitted-code consistency calibration.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import importlib
import importlib.util
import json
from pathlib import Path
import sys

PRIOR_GRAMMAR_SHA256='bdbf5a84ab1a2914e351e917d7ff3994fec5729bddbe33971678cd51c2839119'
UPSTREAM='297ab8df7e5de329605c3875b4934643b371a5e3'
PROVEIT='96836f9eea3540e96322c3d28c7127a582aae223'
RESEARCH_SHA256={
    'recover_wade_dag.py':'caa4996be46f9201991dba07f81d4673f14e874ac682226c29fce9e0cea851f1',
    'theory_backend_experiment.py':'37043e71a02fba57337040100d79e8f92cba5e2ac5efead816b1522b8663a2e1',
    'psc_backend_experiment.py':'33337fc228b1347b7bb942bfdd98511e9d88da24458a9f0b759a5ed90f039902',
    'audit_raw_candidate.py':'cb029edc99925b359bc79ebb6605f109f452292fbcd1e0d6d52b259c8193d41d',
    'psc_adapter_checks.py':'aeae5f034491b90ef27c35850e63da675819cd57d7bae43be6a1aee2f0ce7b5e',
    'pairing_backend_experiment.py':'18f6cf1a50514581834daecd542d9855d07d6c522d4d70f906241de035423572',
}

def transform(nodes,names,seq,grammar):
    """Generalize the prior transform to closed primitive-instruction tokens."""
    out={q:es for q,es in nodes.items() if not 1<=q<=114}
    outnames={q:names[q] for q in out};intern={es:q for q,es in out.items()}
    next_id=max(nodes)+1;refs={}
    def edge(v):return f'ENode {refs[v]}' if isinstance(v,int) else v
    def pair(a,b):
        nonlocal next_id
        es=(a,b)
        if es not in intern:
            intern[es]=next_id;out[next_id]=es;outnames[next_id]=f'closed_grammar_{next_id}';next_id+=1
        return intern[es]
    for j,(a,b) in enumerate(grammar):refs[300+j]=pair(edge(a),edge(b))
    rootedge=edge(seq[-1])
    for v in reversed(seq[:-1]):rootedge=f'ENode {pair(edge(v),rootedge)}'
    root=int(rootedge.split()[1])
    for q in tuple(out):out[q]=tuple(rootedge if e=='ENode 1' else e for e in out[q])
    seen=set();pending=[0]
    while pending:
        q=pending.pop()
        if q in seen:continue
        seen.add(q);pending.extend(int(e.split()[1]) for e in out[q] if e.startswith('ENode '))
    order=[0]+sorted(seen-{0});ids={q:j for j,q in enumerate(order)}
    return ({ids[q]:tuple(f'ENode {ids[int(e.split()[1])]}' if e.startswith('ENode ') else e for e in out[q]) for q in order},
        {ids[q]:outnames[q] for q in order},ids[root])

def strict_repair(word,seed,alpha):
    """Prior Re-Pair, counting non-overlapping occurrences for equal pairs."""
    import random
    rng=random.Random(seed);seq=list(word);grammar=[]
    while True:
        counts=Counter(zip(seq,seq[1:]))
        for a in {a for (a,b),f in counts.items() if a==b and f>=2}:
            hits=0;i=0
            while i+1<len(seq):
                if seq[i]==a and seq[i+1]==a:hits+=1;i+=2
                else:i+=1
            counts[a,a]=hits
        choices=[(p,n) for p,n in counts.items() if n>=2]
        if not choices:break
        pair=rng.choices([p for p,n in choices],[n**alpha for p,n in choices])[0]
        new=[];i=0
        while i<len(seq):
            if i+1<len(seq) and tuple(seq[i:i+2])==pair:new.append(300+len(grammar));i+=2
            else:new.append(seq[i]);i+=1
        assert len(seq)-len(new)>=2
        grammar.append(pair);seq=new
    return seq,grammar

def write_json(path,data):path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--prior-grammar',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();repo=a.repo.resolve();out=a.output.resolve()
    if out==repo or repo in out.parents:ap.error('output must be outside the supplied repository')
    if not __debug__:raise RuntimeError('Do not run with -O; finite checks use assertions')
    prior=a.prior_grammar.resolve()
    if hashlib.sha256(prior.read_bytes()).hexdigest()!=PRIOR_GRAMMAR_SHA256:
        raise ValueError('prior grammar source hash mismatch')
    out.mkdir(parents=True,exist_ok=True)
    research=repo/'Computability/BusyBeaver/Research/ZFC'
    for name,digest in RESEARCH_SHA256.items():
        if hashlib.sha256((research/name).read_bytes()).hexdigest()!=digest:
            raise ValueError('research source hash mismatch: '+name)
    sys.path.insert(0,str(research))
    import recover_wade_dag as r
    import theory_backend_experiment as t
    import psc_backend_experiment as p
    from audit_raw_candidate import normalize_named
    gs=importlib.util.spec_from_file_location('prior_grammar',prior);g=importlib.util.module_from_spec(gs);gs.loader.exec_module(g)
    backend_dir=out/'backend';backend_dir.mkdir(exist_ok=True)
    for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):
        (backend_dir/name).write_bytes(r.git_bytes(None,'ZF/generator/'+name))
    sys.path.insert(0,str(backend_dir));backend=importlib.import_module('TMBuilder')
    nodes,names=r.parse_dag(r.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    _,logical,contract=t.old_contract(nodes)
    summary={'ProveIt_commit':PROVEIT,'upstream_commit':UPSTREAM,'prior_grammar_sha256':PRIOR_GRAMMAR_SHA256,
        'source_sha256':RESEARCH_SHA256,
        'original_contract':contract,'controls':{}}
    for lane in ('original','psc_ir'):
        if lane=='original':
            word=g.axiom_word(nodes);seq,grammar=g.repair(word,341,4)
            ns,na,root=g.transform(nodes,names,seq,grammar)
            cert,stats=g.bisimulation(nodes,ns)
            write_json(out/'original-reference-dag.json',{'root':0,'nodes':nodes,'names':names})
            write_json(out/'original-rm-bisimulation.json',cert)
        else:
            V=t.And(t.Imp(t.Rel('a','b'),t.All('c',t.Rel('a','b'))),
                    t.Imp(t.Eq('a','b'),t.All('c',t.Eq('a','b'))))
            prefix=logical+p.emit(p.psc_template())+t.emit(t.All(1,t.Not(t.Rel(1,1))))+t.emit(V)+t.TAIL
            word=tuple(f'ENode {x}' if isinstance(x,int) else 'EInc 1' if x==p.INC else None for x in prefix)
            assert None not in word
            bc=g.bounder(nodes);assert all(bc(e)==(0,0) for e in word)
            seq,grammar=strict_repair(word,46,4);ns,na,root=transform(nodes,names,seq,grammar)
            stats=None
        machine=g.compile_dag(backend,ns,na);g.reextract(machine,ns,na)
        named=out/f'{lane}-named.tm';machine.save(str(named));numeric,labels,metadata=normalize_named(named.read_bytes())
        count=metadata['working_states'];assert count==(269 if lane=='original' else 283)
        table=out/f'{lane}-{count}.tm';table.write_bytes(numeric)
        write_json(out/f'{lane}-dag.json',{'root':0,'axioms_root':root,'nodes':ns,'names':na})
        write_json(out/f'{lane}-labels.json',labels)
        summary['controls'][lane]={'table':metadata,'decision_states':len(ns),'framework_states':count-len(ns),
            'macro_word_length':len(word),'word':word,'seed':341 if lane=='original' else 46,'exponent':4,
            'grammar_productions':len(grammar),'residual_length':len(seq),'rm_bisimulation':stats,
            'all_original_logical_rows_retained':True,'theory_rows_changed':lane=='psc_ir',
            'original_calculus_and_theory_preserved':lane=='original',
            'PSC_emitted_code_calibration_proved':False,'complete_binary_simulation_proved_here':False,
            'numeric_table_sha256':hashlib.sha256(numeric).hexdigest()}
    write_json(out/'compiler-controls.json',summary)
    print(json.dumps({lane:d['table']['working_states'] for lane,d in summary['controls'].items()}))

if __name__=='__main__':main()
