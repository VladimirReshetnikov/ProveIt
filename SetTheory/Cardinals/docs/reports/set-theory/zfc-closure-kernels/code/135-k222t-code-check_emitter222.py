#!/usr/bin/env python3
"""Independent all-natural emitter and full-source check for conditional G222.

This checker imports neither the candidate constructor nor any search program.
It derives the complete new instruction word from two literal formula changes,
proves their arithmetic macros equivalent to the pinned Dag230 programs, and
checks both independent guarded-CFG resolvers on an independently associated
reference source. Symbolic formula equality covers all natural input codes.
"""
from pathlib import Path
import sys,argparse,json,hashlib
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'support'))
import source_language as s
import tm_tools as tm
import macro_contracts as mc
I,R,Q,E,N,And=mc.I,mc.R,mc.Q,mc.E,mc.N,mc.And

def sha(raw):return hashlib.sha256(raw).hexdigest()
def flat(t):return tuple((o,a) for p,o,a in s.sites(t))
def replace(t,changes):
    if t in changes:return changes[t]
    return t if s.leaf(t) else tuple(replace(v,changes) for v in t)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline-source',type=Path,required=True)
    ap.add_argument('--baseline-table',type=Path,required=True)
    ap.add_argument('--candidate-source',type=Path,required=True)
    ap.add_argument('--dag230',type=Path,default=HERE/'support/Dag230.v')
    ap.add_argument('--proglib230',type=Path,default=HERE/'support/ProgLib230.v')
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    assert __debug__ and not sys.flags.optimize
    assert sha(args.baseline_source.read_bytes())=='b4e453a8801597124fd9b3ee1cd2db1cdf80c0bd904c2ffb59b79d95e91a6e96'
    assert sha(args.baseline_table.read_bytes())=='614adb7d387a5ccdaebecd37d8896d62bb162a20fb8b93b73ec2bd80bd75d785'
    assert sha(args.candidate_source.read_bytes())=='b8f0b7ef8b9f41329509335f844c5fce94ea9b6cfa8f8a3ca7ebb9fe8c736c13'
    parent=s.tree(json.loads(args.baseline_source.read_text()))
    final=s.tree(json.loads(args.candidate_source.read_text()))
    table=tm.read_table(args.baseline_table.read_bytes())
    groups,_=tm.decoder_map(table,parent)
    macros,contracts=mc.bind(groups,args.dag230.read_bytes(),args.proglib230.read_bytes())
    q=lambda k:tm.sole(groups,k)

    # Exact native formula codes; no orthodox-syntax or distinct-label premise.
    a,b,c='a','b','c'
    old_r7=I(E(c,a),I(E(c,b),E(a,b)))
    new_g=I(E(c,a),I(E(c,b),Q(R(a,b),E(a,b))))
    member=R(b,c)
    subset=Q(c,I(R(c,a),R(c,b)))
    request=Q(b,I(c,N(Q(b,I(c,N(member))))))
    closure=Q(a,I(subset,request))
    support=N(Q(a,I(c,N(closure))))
    hereditary=Q(b,I(member,support))
    conditional_core=I(c,N(Q(c,I(member,N(hereditary)))))
    rv=I(R(a,b),Q(c,R(a,b)))
    helper=I(E(a,b),Q(R(a,b),E(a,b)))
    old_bundle=N(I(conditional_core,I(rv,N(helper))))
    new_bundle=And(conditional_core,rv)
    formulas={'old_rho7':old_r7,'merged_G':new_g,'conditional_core':conditional_core,
        'old_bundle':old_bundle,'new_bundle':new_bundle}
    words={name:mc.word(expr) for name,expr in formulas.items()}
    for name,expr in formulas.items():assert mc.execute(words[name])==expr
    leaves={name:mc.flat_word(macros,word) for name,word in words.items()}

    old_flat,new_flat=flat(parent),flat(final)
    assert old_flat[486:786]==leaves['old_rho7']
    assert old_flat[2541:4618]==leaves['old_bundle']
    expected=old_flat[:486]+leaves['merged_G']+old_flat[786:2541]+leaves['new_bundle']+old_flat[4618:]
    assert expected==new_flat
    assert len(leaves['merged_G'])-len(leaves['old_rho7'])==109
    assert len(leaves['new_bundle'])-len(leaves['old_bundle'])==-327
    assert len(old_flat)==4799 and len(new_flat)==4581

    # Different association, generated independently of the candidate tree.
    pc,rel,eq,all_,imp,neg=(q(k) for k in [166,155,182,86,90,184])
    assert flat(rel)==mc.flat_word(macros,[166,121,181])
    assert flat(eq)==mc.flat_word(macros,[166,121,182])
    assert q(207)==((q(99),eq),q(205))
    assert q(153)==(all_,imp)
    gate=q(116)[1][1][1]
    factors_g=[q(99),rel,eq,all_,q(205)]
    factors_bundle=[pc,rel,q(153),neg,imp,neg,gate,q(193)]
    assert all(s.boundary(v)==(0,0,False) for v in factors_g+factors_bundle)
    reference=replace(parent,{q(207):mc.sequence(factors_g),q(224):mc.sequence(factors_bundle)})
    assert flat(reference)==new_flat
    graph,count=s.graph_arithmetic(s.sites(final))
    refgraph,refcount=s.graph_arithmetic(s.sites(reference))
    assert graph==refgraph==s.graph_intervals(s.sites(final))==s.graph_intervals(s.sites(reference))
    receipt=dict(status='EXACT_ALL_NATURAL_CONDITIONAL_G_EMITTER_AND_SOURCE_PASS',
        parent_source_sha256=sha(args.baseline_source.read_bytes()),
        candidate_source_sha256=sha(args.candidate_source.read_bytes()),
        dag230_sha256=mc.DAG_SHA,proglib230_sha256=mc.PROG_SHA,
        primitive_codes={'I':'4*P(x,y)','R':'4*P(x,y)+1','Q':'4*P(x,y)+2','E':'4*P(x,y)+3','F':1},
        formulas=formulas,macro_words=words,macro_contracts=contracts,
        original_row_interval=[486,786],original_bundle_interval=[2541,4618],
        primitive_counts={name:len(seq) for name,seq in leaves.items()},
        old_leaves=4799,new_leaves=4581,all_other_primitives_unchanged=True,
        final_guarded_cases=count,reference_guarded_cases=refcount,independent_graph_resolvers_agree=True,
        gate='Return 0 if c=a or c=b; otherwise And(conditional_K(a,b,c), membership_vacuity(a,b,c)).',
        scope='All natural a,b,c, including low codes and coincident endpoints; arbitrary prior top and stack with inherited clean scratch. Numerical expression equality, all-register macro equivalence and complete source CFG. The logical calibration and binary runtime are separate required certificates.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['status','old_leaves','new_leaves','final_guarded_cases','reference_guarded_cases']},indent=2))

if __name__=='__main__':main()
