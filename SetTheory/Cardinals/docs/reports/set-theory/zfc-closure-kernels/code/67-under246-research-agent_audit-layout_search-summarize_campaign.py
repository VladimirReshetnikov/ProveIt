#!/usr/bin/env python3
"""Consolidate finite-dictionary solver outcomes and check their sources."""
from pathlib import Path
import hashlib,json,re
import grammar_layout as g
import trace_grammar as t
from analyze_candidate import normalizer

HERE=Path(__file__).resolve().parent
metadata=json.loads((g.BASE/'historical/decoder_entries.json').read_text())
entries={int(i):int(max(v,key=v.get)) for i,v in metadata['state_entries'].items()}

def trace_reset(affine):
    t.labels.clear();t.interned.clear();t.affine_symbols.clear()
    t.effects.cache_clear();t.independent.cache_clear()
    t.dependence_predecessors.cache_clear();t.trace_normal.cache_clear()
    t.affine_enabled=affine

records=[]
for path in sorted(HERE.glob('*.json')):
    if not re.match(r'^(dictionary_max|trace.*dictionary.*_max)',path.name):continue
    data=json.loads(path.read_text())
    if 'status' not in data or not isinstance(data['status'],int):continue
    if path.stem.endswith(('_analysis','_sparse')):continue
    kind=data.get('grammar_kind','ordered_closed_association')
    row=dict(file=path.name,sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        grammar_kind=kind,status=data['status'],message=data['message'],
        solver_seconds=data['seconds'],dictionary_phrases=data['phrase_count'],
        model_variables=data['variables'],objective=data.get('objective'),
        frozen_nodes=data.get('freeze',[]),price_objective='modal_entries' if data.get('tm_price') else 'source_nodes')
    if 'nodes' not in data:
        row['conclusion']='No incumbent; this is not a lower-bound certificate.' if data['status']==1 else 'Reported infeasible finite model.'
        records.append(row);continue
    nn={int(i):tuple(map(tuple,p)) for i,p in data['nodes'].items()};root=data['root']
    metrics=(len(nn),*g.rot.zero_metrics(nn,root))
    assert tuple(data['metrics'])==metrics
    if 'trace' in kind:
        trace_reset('affine' in kind)
        oldnorm,oldroot=t.normalize(g.original,g.original_root)
        oldids={oldnorm(('N',n)):n for n in g.original}
        newnorm,newroot=t.normalize(nn,root)
        assert oldroot==newroot,path
    else:
        oldnorm,_=normalizer(g.original);newnorm,_=normalizer(nn)
        oldids={oldnorm(('N',n)):n for n in g.original}
        assert oldnorm(('N',g.original_root))==newnorm(('N',root)),path
    retained=set();fresh=0
    for n in nn:
        key=newnorm(('N',n))
        if key in oldids:retained.add(entries[oldids[key]])
        else:fresh+=1
    row.update(source_equivalence_check='PASS',source_nodes=metrics[0],initial_zero_prefix=metrics[1],
        maximum_zero_run=metrics[2],maximum_path=metrics[3],modal_price=len(retained)+fresh,
        retained_modal_entries=len(retained),fresh_entries=fresh,
        conclusion='Solver reports finite-model optimum.' if data['status']==0 else 'Valid incumbent at time limit; optimality unproved.')
    records.append(row)

result=dict(reference_source_nodes=203,reference_modal_entries=191,
    boundary='All counts refer to source grammars or static modal entries. No result here is a new Turing-machine bound.',
    campaigns=records)
(HERE/'campaign_summary.json').write_text(json.dumps(result,indent=2)+'\n')
for r in records:
    print(r['file'],r.get('source_nodes'),r.get('maximum_zero_run'),r.get('modal_price'),r['status'],r['conclusion'])
