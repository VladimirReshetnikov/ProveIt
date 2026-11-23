#!/usr/bin/env python3
"""Reproducible exhaustive small-input checks; these are not formal proofs."""
from __future__ import annotations
import json
import platform
import time
from itertools import product
from pathlib import Path
from proplogic import *


def formulas(max_nodes):
    by={1:[BOT,Var(0),Var(1)]}
    for n in range(3,max_nodes+1,2):
        by[n]=[Formula(tag,(a,b)) for i in range(1,n-1,2)
               for a in by[i] for b in by[n-1-i] for tag in ('and','or','imp')]
    return [a for n in sorted(by) for a in by[n]]


def main():
    start=time.monotonic(); counts={}
    fs=formulas(5); counts['formulas_exhausted_max_nodes_5_two_variables']=len(fs)
    for a in fs:
        assert equivalent(a,canonical_dnf(a))
        assert equivalent(a,canonical_cnf(a))
    counts['canonical_normal_form_equivalences']=2*len(fs)

    sigmas=[dict(enumerate(s)) for s in product((BOT,Var(0),Var(1),Not(Var(0)),And(Var(0),Var(1))),repeat=2)]
    count=0
    for a in fs:
        for sigma in sigmas:
            for v in valuations((0,1)):
                assert evaluate(substitute(a,sigma),v)==evaluate(a,{i:evaluate(sigma[i],v) for i in (0,1)})
                count+=1
    counts['substitution_semantic_equalities']=count

    count=0
    for a in fs:
        t=tseitin(a)
        assert all(len(c)<=3 for c in t.clauses)
        assert len(t.definitions)<=nodes(a)
        for v in valuations(variables(a)):
            assert cnf_value(t.clauses,t.extend(v))==evaluate(a,v)
            extra=cnf_variables(t.clauses)-variables(a)
            matches=0
            for extension in valuations(extra):
                w={**v,**extension}
                if cnf_value(t.clauses,w):
                    matches+=1; assert evaluate(a,v)
                    assert all(w[z]==evaluate(b,v) for z,b in t.definitions)
                count+=1
            assert matches==int(evaluate(a,v))
    counts['tseitin_extension_assignments']=count

    # Exhaust all 2^(3^2)=512 sets of non-tautological clauses on p0,p1.
    all_clauses=[frozenset((i+1)*s for i,s in enumerate(signs) if s)
                 for signs in product((-1,0,1),repeat=2)]
    count=0
    for selector in product((False,True),repeat=len(all_clauses)):
        cs=frozenset(c for use,c in zip(selector,all_clauses) if use)
        sat=any(cnf_value(cs,v) for v in valuations((0,1)))
        closure,proof=resolution_closure(cs)
        assert check_resolution(cs,proof)
        assert (frozenset() in closure)==(not sat)
        witness=dpll(cs)
        assert (witness is not None)==sat
        if witness is not None: assert cnf_value(cs,witness)
        count+=1
    counts['exhaustive_two_variable_cnf_resolution_dpll_instances']=count

    count=0
    for a in fs:
        av=sorted(variables(a))
        for mask in range(1<<len(av)):
            forgotten={av[i] for i in range(len(av)) if mask&(1<<i)}
            b=forget(a,forgotten)
            assert variables(b)<=variables(a)-forgotten
            for v in valuations(variables(a)-forgotten):
                assert evaluate(b,v)==any(evaluate(a,{**v,**u}) for u in valuations(forgotten))
                count+=1
    counts['forgetting_projection_equalities']=count

    small=formulas(3)
    # Renaming creates also disjoint/shared/private support configurations.
    right=small+[substitute(b,{0:Var(2)}) for b in small]
    count=0
    for a in small:
        for b in right:
            if all(not evaluate(a,v) or evaluate(b,v) for v in valuations(variables(a)|variables(b))):
                it=interpolant(a,b)
                assert variables(it)<=variables(a)&variables(b)
                assert all(not evaluate(a,v) or evaluate(it,v) for v in valuations(variables(a)|variables(it)))
                assert all(not evaluate(it,v) or evaluate(b,v) for v in valuations(variables(b)|variables(it)))
                count+=1
    counts['valid_entailments_with_interpolant_checked']=count

    p,q=Var(0),Var(1); chain=Kripke((frozenset((0,1)),frozenset((1,))),((0,frozenset((1,))),))
    fork=Kripke((frozenset((0,1,2)),frozenset((1,)),frozenset((2,))),((0,frozenset((1,))),))
    assert chain.valid() and fork.valid()
    assert not Kripke((),()).valid()
    counts['empty_kripke_frame_rejections']=1
    refuted=[Or(p,Not(p)),Imp(Not(Not(p)),p),Imp(Imp(Imp(p,q),p),p),Imp(Imp(p,p),Or(Not(p),p))]
    assert all(not chain.forces(0,a) for a in refuted)
    assert not fork.forces(0,Or(Not(p),Not(Not(p))))
    fork_pq=Kripke((frozenset((0,1,2)),frozenset((1,)),frozenset((2,))),
                   ((0,frozenset((1,))),(1,frozenset((2,)))))
    further=[Or(Imp(p,q),Imp(q,p)),
             Imp(Not(And(p,q)),Or(Not(p),Not(q))),
             Imp(Not(Not(Or(p,q))),Or(Not(Not(p)),Not(Not(q))))]
    assert fork_pq.valid() and all(not fork_pq.forces(0,a) for a in further)
    s=Var(2)
    three_leaves=Kripke((frozenset((0,1,2,3)),frozenset((1,)),frozenset((2,)),frozenset((3,))),
                        ((0,frozenset((1,))),(1,frozenset((2,))),(2,frozenset((3,)))))
    kreisel_putnam=Imp(Imp(Not(p),Or(q,s)),Or(Imp(Not(p),q),Imp(Not(p),s)))
    assert three_leaves.valid() and not three_leaves.forces(0,kreisel_putnam)
    counts['explicit_classical_only_principles_refuted']=9

    # Regression against the non-tautology printed in the source article.
    r=Var(2)
    article_formula=Imp(p,Imp(Or(q,r),Imp(r,Not(p))))
    assert not evaluate(article_formula,{0:True,1:False,2:True})
    counts['source_article_non_tautology_regressions']=1

    targeted=[(Or(p,Not(p)),False), (Imp(Not(Not(p)),p),False),
              (Imp(Imp(Imp(p,q),p),p),False),
              (Or(Not(p),Not(Not(p))),False),
              (Not(Not(Or(p,Not(p)))),True),
              (Imp(p,Not(Not(p))),True),
              (Imp(And(p,Or(q,r)),Or(And(p,q),And(p,r))),True)]
    for a,expected in targeted:
        d=ipc_saturate((),a)
        assert check_nd(d.proof_nodes,False) and d.model.valid() and d.truth_lemma()
        assert d.derivable((),a)==expected
    counts['ipc_targeted_decisions_and_canonical_truth_lemmas']=len(targeted)

    # Check every saturated sequent has a valid IPC proof DAG, every finite
    # canonical model is valid, and every subformula satisfies its truth lemma.
    max_worlds=max_rounds=max_m=max_nodes=0; count=0
    for a in fs:
        decision=ipc_saturate((),a)
        assert check_nd(decision.proof_nodes,classical=False)
        assert decision.model.valid() and decision.truth_lemma()
        provable=decision.derivable((),a)
        assert provable==all(decision.model.forces(w,a) for w in range(len(decision.worlds)))
        if provable:
            assert all(evaluate(a,v) for v in valuations(variables(a)))
        else:
            assert any(not decision.model.forces(w,a) for w in range(len(decision.worlds)))
        max_worlds=max(max_worlds,len(decision.worlds)); max_rounds=max(max_rounds,decision.rounds)
        max_m=max(max_m,len(decision.formulas)); max_nodes=max(max_nodes,len(decision.proof_nodes)); count+=1
    counts['ipc_saturation_proof_dags_and_canonical_models']=count
    counts['ipc_max_formula_universe_size']=max_m
    counts['ipc_max_canonical_worlds']=max_worlds
    counts['ipc_max_saturation_scans']=max_rounds
    counts['ipc_max_proof_dag_nodes']=max_nodes

    # Context-sensitive checks: conjunction and disjunction elimination, and
    # discharge of an antecedent in implication introduction.
    contexts=[(p,), (Or(p,q),Imp(p,q)), (Imp(p,q),p), (Not(p),p), (And(p,q),)]
    goals=[p,q,BOT,And(p,q),Or(p,q),Imp(p,q),Imp(p,p)]
    for g in contexts:
        for a in goals:
            d=ipc_saturate(g,a)
            assert check_nd(d.proof_nodes,False) and d.model.valid() and d.truth_lemma()
            entails=all(not all(d.model.forces(w,b) for b in g) or d.model.forces(w,a)
                        for w in range(len(d.worlds)))
            assert d.derivable(g,a)==entails
    counts['ipc_context_sequents']=len(contexts)*len(goals)

    ipc_proofs=ipc_models=cpc_proofs=cpc_values=0
    export_cases=[((),a) for a in fs]+[(g,a) for g in contexts for a in goals]
    for g,a in export_cases:
        ri=decide_ipc(g,a)
        assert check_ipc_result(ri)
        assert check_ipc_result(result_from_data(json.loads(json.dumps(result_data(ri)))))
        if isinstance(ri,ProofResult):
            ipc_proofs+=1
            assert ri.root==len(ri.proof)-1
        else:
            ipc_models+=1
            assert ri.world==0 and ri.model.up[0]==frozenset(range(len(ri.model.up)))
        rc=truth_table_prove(g,a)
        assert check_cpc_result(rc)
        assert check_cpc_result(result_from_data(json.loads(json.dumps(result_data(rc)))))
        if isinstance(rc,ProofResult):
            cpc_proofs+=1
            assert rc.root==len(rc.proof)-1
        else: cpc_values+=1
    counts['ipc_exported_proofs_replayed']=ipc_proofs
    counts['ipc_exported_rooted_countermodels_replayed']=ipc_models
    counts['cpc_truth_table_constructed_proofs_replayed']=cpc_proofs
    counts['cpc_exported_countervaluations_replayed']=cpc_values
    counts['certificate_json_roundtrips_replayed']=2*len(export_cases)

    ipc_lem_result=decide_ipc((),Or(p,Not(p)))
    cpc_lem_result=truth_table_prove((),Or(p,Not(p)))
    assert isinstance(ipc_lem_result,IPCCountermodelResult)
    assert isinstance(cpc_lem_result,ProofResult)
    assert not check_ipc_result(cpc_lem_result)
    assert not check_nd(cpc_lem_result.proof,False)
    article_result=truth_table_prove((),article_formula)
    assert isinstance(article_result,BooleanCountervaluationResult) and check_cpc_result(article_result)
    counts['public_witness_export_mode_and_article_regressions']=3

    lem=NDNode(frozenset(),Or(p,Not(p)),'lem')
    assert check_nd([lem],True) and not check_nd([lem],False)
    assert not check_nd([NDNode(frozenset(),p,'hyp')])
    assert not check_nd([NDNode(frozenset((p,)),p,'hyp',(0,))])
    assert not check_nd([NDNode(frozenset(),p,'magic')])
    hyp_p=NDNode(frozenset((p,)),p,'hyp')
    hyp_q=NDNode(frozenset((q,)),q,'hyp')
    bad_dags=[
        [hyp_p,NDNode(frozenset(),p,'weak',(0,))],
        [hyp_q,NDNode(frozenset(),Imp(p,q),'impI',(0,))],
        [NDNode(frozenset((Imp(p,q),)),Imp(p,q),'hyp'),hyp_p,
         NDNode(frozenset((Imp(p,q),)),q,'impE',(0,1))],
        [NDNode(frozenset((p,)),q,'hyp')],
        [NDNode(frozenset((p,)),p,'weak',(1,)),hyp_p],
        [NDNode(frozenset((p,)),p,'weak',(-1,))],
        [NDNode(frozenset(),Or(p,p),'lem')],
    ]
    assert all(not check_nd(d,True) for d in bad_dags)
    assert check_nd_conclusion([hyp_p],0,(p,),p)
    assert not check_nd_conclusion([hyp_p],0,(),p)
    assert not check_nd_conclusion([hyp_p],0,(p,),q)
    assert not check_nd_conclusion([],0,(),p)
    counts['proof_checker_negative_or_mode_tests']=4+len(bad_dags)+3
    counts['proof_checker_exact_target_positive_tests']=1

    result={'status':'all checks passed','python':platform.python_version(),
            'elapsed_seconds':round(time.monotonic()-start,3),'counts':counts,
            'scope':'Exhaustive small-input executable validation; not a formal iPRA or Lean verification.',
            'lean_status':'Lean compiler unavailable; Lean sources are uncompiled proof candidates.'}
    destination=Path(__file__).with_name('validation_results.json')
    destination.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
