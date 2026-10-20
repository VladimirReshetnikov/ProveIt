#!/usr/bin/env python3
"""Independent exact arithmetic-emitter and whole-source check for seed-G222.

This program imports no candidate constructor. It reconstructs the full new
instruction word directly from two formula edits, verifies all-register macro
bisimulations to pinned Dag230, and checks two independent complete CFGs.
"""
from pathlib import Path
import argparse,hashlib,json,sys

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--support-dir',type=Path,required=True)
    ap.add_argument('--baseline-source',type=Path,required=True)
    ap.add_argument('--baseline-table',type=Path,required=True)
    ap.add_argument('--candidate-source',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    sys.path.insert(0,str(args.support_dir.resolve()))
    import source_language as s
    import tm_tools as tm
    import macro_contracts as mc
    I,R,Q,E,N=mc.I,mc.R,mc.Q,mc.E,mc.N
    sha=lambda data:hashlib.sha256(data).hexdigest()
    assert __debug__ and not sys.flags.optimize
    assert sha(args.baseline_source.read_bytes())=='df55079f114a6aa9ada970d7d857726e47e3a3dba2a721245ebbacfd4577c13c'
    assert sha(args.baseline_table.read_bytes())=='7e036b1bd05fe8a7e5877a8c5386cae603f4d689adeeb13754ee98dca998bfef'
    parent=s.tree(json.loads(args.baseline_source.read_text()))
    final=s.tree(json.loads(args.candidate_source.read_text()))
    table=tm.read_table(args.baseline_table.read_bytes())
    groups,_=tm.decoder_map(table,parent)
    macros,contracts=mc.bind(groups,(args.support_dir/'Dag230.v').read_bytes(),(args.support_dir/'ProgLib230.v').read_bytes())
    q=lambda state:tm.sole(groups,state)
    flat=lambda tree:tuple((op,arg) for path,op,arg in s.sites(tree))
    a,b,c='a','b','c'
    member=R(b,c)
    subset=Q(c,I(R(c,a),R(c,b)))
    request=Q(b,I(c,N(Q(b,I(c,N(member))))))
    closure=Q(a,I(subset,request))
    support=N(Q(a,I(c,N(closure))))
    hereditary=Q(b,I(member,support))
    rv=I(R(a,b),Q(c,R(a,b)))
    helper=I(E(a,b),Q(R(a,b),E(a,b)))
    fused_seed=Q(c,I(hereditary,N(request)))
    old_bundle=N(I(rv,I(helper,fused_seed)))
    new_bundle=N(I(rv,fused_seed))
    old_rho=I(E(c,a),I(E(c,b),E(a,b)))
    new_g=I(E(c,a),I(E(c,b),Q(R(a,b),E(a,b))))
    formulas={'old_rho7':old_rho,'new_G':new_g,'old_bundle':old_bundle,'new_bundle':new_bundle}
    words={name:mc.word(expr) for name,expr in formulas.items()}
    leaves={name:mc.flat_word(macros,word) for name,word in words.items()}
    for name,expr in formulas.items():assert mc.execute(words[name])==expr
    assert len(words['old_bundle'])==77 and len(words['new_bundle'])==65
    oldflat,newflat=flat(parent),flat(final)
    assert oldflat[486:786]==leaves['old_rho7']
    assert oldflat[2541:4781]==leaves['old_bundle']
    expected=oldflat[:486]+leaves['new_G']+oldflat[786:2541]+leaves['new_bundle']+oldflat[4781:]
    assert expected==newflat
    assert len(oldflat)==4962 and len(newflat)==4744
    assert len(leaves['new_G'])-len(leaves['old_rho7'])==109
    assert len(leaves['new_bundle'])-len(leaves['old_bundle'])==-327

    # Independent reference: replace one closed ancestor with a flat sequence
    # of closed macro blocks. No literal optimized grammar is read here.
    target='11101001001110'
    ax=s.subtree(parent,target)
    assert len(flat(ax))==4167
    def chunks(node,first,last):
        result=[]
        def visit(n,start):
            end=start+len(flat(n))
            if end<=first or last<=start:return
            if first<=start and end<=last:
                assert s.boundary(n)==(0,0,False);result.append(n);return
            assert not s.leaf(n)
            visit(n[0],start);visit(n[1],start+len(flat(n[0])))
        visit(node,0);return result
    rel,eq,all_=q(155),q(182),q(86)
    assert flat(rel)==mc.flat_word(macros,[166,121,181])
    assert flat(eq)==mc.flat_word(macros,[166,121,182])
    assert flat(ax)[:84]==flat((q(99),eq))
    factors=[q(99),rel,eq,all_]+chunks(ax,84,1893)+[macros[k] for k in words['new_bundle']]+chunks(ax,4133,4167)
    assert all(s.boundary(t)==(0,0,False) for t in factors)
    reference=s.replace(parent,target,mc.sequence(factors))
    assert flat(reference)==newflat
    graph,count=s.graph_arithmetic(s.sites(final));refgraph,refcount=s.graph_arithmetic(s.sites(reference))
    assert graph==refgraph==s.graph_intervals(s.sites(final))==s.graph_intervals(s.sites(reference))
    receipt=dict(status='EXACT_ALL_NATURAL_SEED_G_EMITTER_AND_SOURCE_PASS',
        parent_source_sha256=sha(args.baseline_source.read_bytes()),parent_table_sha256=sha(args.baseline_table.read_bytes()),
        candidate_source_sha256=sha(args.candidate_source.read_bytes()),
        dag230_sha256=mc.DAG_SHA,proglib230_sha256=mc.PROG_SHA,
        primitive_codes={'I':'4*P(x,y)','R':'4*P(x,y)+1','Q':'4*P(x,y)+2','E':'4*P(x,y)+3','F':1},
        formulas=formulas,macro_words=words,macro_contracts=contracts,
        original_row_interval=[486,786],original_bundle_interval=[2541,4781],
        old_leaves=4962,new_leaves=4744,all_other_primitives_unchanged=True,
        final_guarded_cases=count,reference_guarded_cases=refcount,independent_graph_resolvers_agree=True,
        gate='Return 0 if c=a or c=b; otherwise And(membership_vacuity(a,b,c), seed_K(a,b,c)).',
        scope='All natural a,b,c, including low codes and coincident endpoints; arbitrary prior top/stack with clean scratch. Exact symbolic expressions, all-register macro equivalence, complete source CFG. Native calculus equivalence and binary runtime are separate obligations.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in('status','old_leaves','new_leaves','final_guarded_cases','reference_guarded_cases')},indent=2))

if __name__=='__main__':main()
