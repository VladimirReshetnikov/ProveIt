#!/usr/bin/env python3
"""Three-variable congruence fusion, with full compiled framework costs.

Research control only: the emitted axiom families are propositionally
interderivable with the original rows; this script does not establish the
binary compiler's complete consistency simulation.
"""
from __future__ import annotations
import argparse
from collections import Counter
import copy
import importlib
import itertools
import json
from pathlib import Path
import sys
import time

BASE = Path(__file__).resolve().parent


def default_repository():
    for candidate in [BASE/'proveit',BASE,*BASE.parents,Path.cwd()]:
        if (candidate/'Computability/BusyBeaver/Research/ZFC').is_dir():
            return candidate
    return BASE/'proveit'


def formula(variables, order, grouping):
    a,b,c=variables
    es=[t.Imp(t.Eq(c,b),t.Eq(a,b)),
        t.Imp(t.Rel(c,b),t.Rel(a,b)),
        t.Imp(t.Rel(b,c),t.Rel(b,a))]
    x,y,z=[es[i] for i in order]
    body=t.And(t.And(x,y),z) if grouping==0 else t.And(x,t.And(y,z))
    return t.Imp(t.Eq(c,a),body)


def check_certificate_mutations(checker,engine,out):
    original=json.loads((out/'rm_certificate.json').read_text())
    results=[]
    for kind in ['wrong_operation','wrong_successor','wrong_initial',
                 'missing_pair','duplicate_pair']:
        changed=copy.deepcopy(original)
        if kind=='wrong_operation':
            changed['pairs'][0]['instruction']='EHalt'
        elif kind=='wrong_successor':
            changed['pairs'][0]['successors'][0]=len(changed['pairs'])
        elif kind=='wrong_initial':changed['initial']=1
        elif kind=='missing_pair':changed['pairs'].pop()
        else:changed['pairs'].append(copy.deepcopy(changed['pairs'][0]))
        path=out/f'negative-{kind}.json'
        path.write_text(json.dumps(changed)+'\n')
        rejected=False
        try:
            checker(engine,out/'reference_dag.json',out/'candidate_dag.json',path)
        except (AssertionError,ValueError,KeyError,IndexError):
            rejected=True
        path.unlink()
        if not rejected:raise ValueError('Corrupt certificate accepted: '+kind)
        results.append({'mutation':kind,'rejected':True})
    return results


def main():
    global t,r,g,layout
    if not __debug__:raise RuntimeError('Run without -O; verification uses assertions')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=default_repository())
    ap.add_argument('--output',type=Path,default=BASE/'route_fusion_output')
    ap.add_argument('--seeds',type=int,default=8)
    ap.add_argument('--positions',type=int,nargs='+',default=[1,2,3,4,5])
    ap.add_argument('--exponents',type=int,nargs='+',default=[4])
    ap.add_argument('--lanes',nargs='+',default=['primitive'])
    args=ap.parse_args()
    research=args.repo.resolve()/'Computability/BusyBeaver/Research/ZFC'
    if not research.is_dir():
        ap.error('--repo must point to the pinned ProveIt checkout')
    sys.path.insert(0,str(research))
    import theory_backend_experiment as t
    import recover_wade_dag as r
    import full_grammar_experiment as g
    import layout_grammar_experiment as layout
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    helper=g.load_file('route_fusion_helper',g.REPORT/'code/08-schema-machine-rebracket_axioms.py')
    engine=g.load_file('route_fusion_engine',g.REPORT/'code/08-schema-machine-verify_rm_certificate.py')
    nodes,names=r.parse_dag(r.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    original_word,logical,_=t.old_contract(nodes)
    selected_word,_=layout.selected_word(nodes)
    bundle_word=selected_word[len(logical):-len(t.TAIL)]
    spec,_=t.published_spec();rows=spec['ax_rows']('a','h','b','c','u')
    bundle=t.symbolic(bundle_word,initial_b='b')[0][-1]
    other_rows=[rows[i] for i in [1,3,5,7,8]]
    original_leaves=layout.framework_leaves(nodes)
    for name in ['TMBuilder.py','tm.py','tmdb.py','LICENSE.wade']:
        (out/name).write_bytes(r.git_bytes(None,'ZF/generator/'+name))
    sys.path.insert(0,str(out));backend=importlib.import_module('TMBuilder')
    baseline=helper.compile_dag(backend,nodes,names)
    assert len({q for q,_ in baseline.states})==281
    histogram=Counter();best=None;trials=0;start=time.monotonic();frames={}
    for variables,order,grouping,position in itertools.product(
            itertools.permutations('abc'),itertools.permutations(range(3)),
            [0,1],args.positions):
        fusion=formula(variables,order,grouping)
        newrows=other_rows[:position]+[fusion]+other_rows[position:]
        word=[166,121,180,176]+[q for row in newrows for q in t.emit(row)]+bundle_word+t.TAIL
        assert t.symbolic(word)[0]==['old_top',rows[0],*newrows,bundle]
        assert len(t.emit(fusion))==27
        lanes=layout.tokenizations(nodes,word)
        for lane,alpha,seed in itertools.product(args.lanes,args.exponents,range(args.seeds)):
            tokens=lanes[lane]
            seq,grammar,_=g.safe_repair(tokens,seed,alpha)
            nn,nm,root=layout.transform(nodes,names,tokens,seq,grammar)
            assert layout.framework_leaves(nn)==original_leaves
            depth=layout.dispatch_depth(nn);cost=len(nn)+55+depth
            if depth not in frames:
                tm=helper.compile_dag(backend,nn,nm);helper.reextract(tm,nn,nm)
                actual=len({q for q,_ in tm.states});assert actual==cost
                frames[depth]={'nodes':len(nn),'framework':55+depth,'actual_states':actual}
            histogram[cost]+=1;trials+=1
            key=(cost,len(nn),len(grammar),len(seq),variables,order,grouping,position,lane,alpha,seed)
            if best is None or key<best['key']:
                best=dict(key=key,nodes=nn,names=nm,root=root,word=word,
                    tokens=tokens,residual=seq,productions=grammar,
                    variables=variables,order=order,grouping=grouping,position=position,
                    lane=lane,exponent=alpha,seed=seed,depth=depth)
                print(json.dumps({'best':cost,'nodes':len(nn),'framework':55+depth,
                    'trial':trials,'recipe':list(key[4:]),'seconds':time.monotonic()-start}),flush=True)
    assert best is not None
    write=lambda name,data:(out/name).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    refn,refm,refr=layout.transform(nodes,names,best['word'],best['word'],[])
    write('reference_dag.json',dict(root=0,nodes=refn,names=refm,axioms_root=refr))
    write('candidate_dag.json',dict(root=0,nodes=best['nodes'],names=best['names'],axioms_root=best['root']))
    cert,stats=helper.bisimulation(refn,best['nodes']);write('rm_certificate.json',cert)
    independently=layout.independent_check(engine,out/'reference_dag.json',out/'candidate_dag.json',out/'rm_certificate.json')
    mutations=check_certificate_mutations(layout.independent_check,engine,out)
    tm=helper.compile_dag(backend,best['nodes'],best['names']);helper.reextract(tm,best['nodes'],best['names'])
    table,labels,missing=g.normalize(tm);(out/'candidate.tm').write_bytes(table)
    tm.save(str(out/'candidate.named.tm'))
    write('labels.json',labels)
    write('recipe.json',{k:v for k,v in best.items() if k not in ['nodes','names']})
    result=dict(upstream_commit=r.COMMIT,baseline_states=281,
        prior_complete_control=268,working_states=best['key'][0],
        decision_nodes=len(best['nodes']),framework_states=55+best['depth'],
        recipe={k:best[k] for k in ['variables','order','grouping','position','lane','exponent','seed']},
        ax_word_macros=len(best['word']),prior_ax_word_macros=len(selected_word),
        original_congruence_macros=sum(len(t.emit(rows[i])) for i in [2,4,6]),
        fused_congruence_macros=27,trials=trials,histogram=dict(sorted(histogram.items())),
        actual_framework_checks=frames,rm_certificate=independently,
        negative_certificate_checks=mutations,
        elapsed_seconds=time.monotonic()-start,
        native_full_equality_calculus_equivalence='ordinary_propositional_proof',
        binary_machine_consistency_theorem=False,new_state_record=False)
    write('results.json',result);print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
