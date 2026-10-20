#!/usr/bin/env python3
"""Bind the literal G223 source to its exact all-natural numerical calculus.

The checker compares symbolic arithmetic expression trees, not sampled values.
It also compares the complete primitive instruction word and two independent
resolvers of the complete guarded control-flow graph. The logical equivalence
of the old and new calculi is proved in a separate finite proof certificate.
"""
from pathlib import Path
from functools import cache
import argparse, hashlib, importlib.util, json, re, sys

PARENT_SOURCE='309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878'
PARENT_TABLE='4526bd8cf2160ac5dfce039add0550e9788095f60ecc6b4462afd4ebbfd42790'
FINAL_SOURCE='fe3713adaf008a71ba4fbc6433de760ef124b8638efbc5c75e3afa2c1142c24f'
DAG230='7f44c6bc6cb2e5a7a30c1267738c8df7bfd8e036987721ac0bb6bdc326e54eaf'
sha=lambda raw:hashlib.sha256(raw).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline224',type=Path,required=True)
    ap.add_argument('--upstream226',type=Path,required=True)
    ap.add_argument('--sites',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args()
    sys.path.insert(0,str(a.upstream226/'verification'))
    import reconstruct227 as c
    sys.path.insert(0,str(a.baseline224/'portable/verification'))
    import construct_rel225 as cr
    emitter=a.baseline224/'portable/verification/check_emitter.py'
    assert sha(emitter.read_bytes())=='32fa8462a8ab95fbcd2969faf915f0a6fb872484723ae355297624c5d843d93f'
    spec=importlib.util.spec_from_file_location('pinned_old_emitter',emitter)
    old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
    I,R,Q,E,N,A=old.I,old.R,old.Q,old.E,old.N,old.A
    parent_path=a.baseline224/'portable/parent225/sites225.json'
    table_path=a.baseline224/'portable/parent225/candidate225.k.tm'
    assert sha(parent_path.read_bytes())==PARENT_SOURCE
    assert sha(table_path.read_bytes())==PARENT_TABLE
    assert sha(a.sites.read_bytes())==FINAL_SOURCE
    parent=c.tree(json.loads(parent_path.read_text()))
    final=c.tree(json.loads(a.sites.read_text()))
    groups,_=cr.decoder_map(c,cr.read_table(table_path),parent)
    q=lambda k:cr.sole(groups,k)
    def flat(t):return tuple((o,v) for p,o,v in c.sites(t))
    def seq(parts):
        assert parts
        return parts[0] if len(parts)==1 else (parts[0],seq(parts[1:]))
    def replace(t,changes):
        if t in changes:return changes[t]
        return t if c.leaf(t) else tuple(replace(v,changes) for v in t)

    # Recover the explicitly pinned upstream macro programs. Their contracts
    # are the ProgLib230 lemmas replayed by the supplied baseline package.
    dag_path=a.upstream226/'vendor/k230-rocq/coq/prog/Dag230.v'
    data=dag_path.read_bytes();assert sha(data)==DAG230
    nodes={int(k):(x,y) for k,x,y in re.findall(r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)',data.decode())}
    primitive={'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'}
    @cache
    def edge(s):
        parts=s.split();kind=parts[0];n=int(parts[1]) if len(parts)>1 else 0
        if kind=='ENode':return tuple(edge(v) for v in nodes[n])
        return primitive[kind],n
    def macro(k):return edge('ENode '+str(k))
    macros={166,121,168,171,177,119,181,182,180,218,178,183,176,158,208,192,131,211,197}
    @cache
    def expand(k):
        if k in macros:return (k,)
        out=()
        for ed in nodes[k]:
            kind,n=ed.split();assert kind=='ENode';out+=expand(int(n))
        return out
    ax=list(expand(236));assert len(ax)==154
    macro_bindings={166:q(98),121:q(12),168:q(166),171:q(19),177:q(184)[0],119:q(90),
                    180:q(86),181:(q(90),('CI',1)),182:(q(86),('CI',1)),218:q(184),
                    178:(q(184),(q(90),q(184))),183:(q(184),(q(86),q(184)))}
    contracts=[]
    for k,p in macro_bindings.items():
        ref=macro(k)
        assert c.boundary(p)==c.boundary(ref)==(0,0,False)
        bisimulation=cr.local_bisimulation(ref,p)
        gp,np=c.graph_arithmetic(c.sites(p));gr,nr=c.graph_arithmetic(c.sites(ref))
        assert gp==c.graph_intervals(c.sites(p)) and gr==c.graph_intervals(c.sites(ref))
        contracts.append(dict(upstream_macro=k,primitive_instructions=len(flat(p)),all_register_bisimulation=bisimulation,
                              checks_current=np,checks_upstream=nr))
    def word_flat(word):return sum((flat(macro_bindings[k]) for k in word),())

    # Exact numerical row. Symbolic expression equality means equality for all
    # natural a,b,c, including codes not corresponding to orthodox syntax.
    old_r7=[168,166,182,168,121,182,166,121,182,119,119]
    new_g=[168,166,182,168,121,182,166,121,181,166,121,182,180,119,119]
    assert ax[19:30]==old_r7
    old_r7_formula=I(E('c','a'),I(E('c','b'),E('a','b')))
    g_formula=I(E('c','a'),I(E('c','b'),Q(R('a','b'),E('a','b'))))
    assert old.execute(old_r7)==old_r7_formula
    assert old.execute(new_g)==g_formula

    # Recover the exact canonical fused bundle word from the old pinned AX
    # word; then omit H and use one conjunction instead of the old fused pair.
    canonical_word=[];i=88;fusions=0
    while i<149:
        if i==141:
            assert ax[i]==168;canonical_word.extend((166,121,181));i+=1
        elif ax[i:i+2]==[178,183]:
            canonical_word.extend((218,119,180,218));i+=2;fusions+=1
        elif i==147:
            assert ax[i:i+2]==[178,178];canonical_word.extend((218,119,119,218));i+=2
        else:canonical_word.append(ax[i]);i+=1
    assert fusions==3
    rv_word=[166,121,181,168,166,121,181,180,119]
    h_word=[166,121,182,166,121,181,166,121,182,180,119]
    old_suffix=rv_word+h_word+[218,119,119,218]
    assert canonical_word[-len(old_suffix):]==old_suffix
    core_word=canonical_word[:-len(old_suffix)]
    new_bundle_word=core_word+rv_word+[218,119,218]
    core=old.execute(core_word)
    rv=I(R('a','b'),Q('c',R('a','b')))
    h=I(E('a','b'),Q(R('a','b'),E('a','b')))
    canonical=old.formulas()[2]
    assert old.execute(canonical_word)==canonical==N(I(core,I(rv,N(h))))
    new_bundle=A(core,rv)
    assert old.execute(new_bundle_word)==new_bundle

    # Compare every literal primitive leaf, rather than only the named subtrees
    # or formula expressions. These are the only two instruction-word changes.
    old_flat=flat(parent);new_flat=flat(final)
    old_r7_flat,new_g_flat=word_flat(old_r7),word_flat(new_g)
    old_bundle_flat,new_bundle_flat=word_flat(canonical_word),word_flat(new_bundle_word)
    assert old_flat[486:786]==old_r7_flat
    places=[i for i in range(len(old_flat)-len(old_bundle_flat)+1) if old_flat[i:i+len(old_bundle_flat)]==old_bundle_flat]
    assert len(places)==1;bundle_start=places[0];bundle_end=bundle_start+len(old_bundle_flat)
    assert 786<=bundle_start
    expected=(old_flat[:486]+new_g_flat+old_flat[786:bundle_start]+new_bundle_flat+old_flat[bundle_end:])
    assert expected==new_flat
    assert len(new_g_flat)-len(old_r7_flat)==109
    assert len(new_bundle_flat)-len(old_bundle_flat)==-327

    # Build a direct closed-macro reference program, independent of the
    # optimized source tree and compiler. All remaining blocks are literal old
    # blocks. Two independent guarded-CFG resolvers prove exact local branching
    # and every continue/break target in the complete new source.
    pc,rel,eq,all_,imp,neg=(q(k) for k in [166,155,182,86,90,184])
    assert flat(rel)==word_flat([166,121,181])
    assert flat(eq)==word_flat([166,121,182])
    assert q(207)==((q(99),eq),q(205))
    gate=q(116)[1][1][1]
    factors_g=[q(99),rel,eq,all_,q(205)]
    factors_bundle=[pc,rel,q(153),neg,imp,neg,gate,q(193)]
    assert q(153)==(all_,imp)
    assert all(c.boundary(v)==(0,0,False) for v in factors_g+factors_bundle)
    reference=replace(parent,{q(207):seq(factors_g),q(224):seq(factors_bundle)})
    assert flat(reference)==new_flat
    gf,nf=c.graph_arithmetic(c.sites(final));gr,nr=c.graph_arithmetic(c.sites(reference))
    assert gf==gr==c.graph_intervals(c.sites(final))==c.graph_intervals(c.sites(reference))

    prog=a.upstream226/'vendor/k230-rocq/coq/prog/ProgLib230.v'
    assert sha(prog.read_bytes())=='6af4a13b2034b867054f5b74e7635a305172b6a45f58db91dffe63ae57d50dbb'
    result=dict(status='EXACT_ALL_NATURAL_EMITTER_AND_COMPLETE_SOURCE_BINDING_PASS',
        source_sha256=FINAL_SOURCE,parent_source_sha256=PARENT_SOURCE,
        upstream_dag_sha256=DAG230,upstream_macro_contracts_sha256=sha(prog.read_bytes()),
        primitive_codes={'I':'4*P(x,y)','R':'4*P(x,y)+1','Q':'4*P(x,y)+2','E':'4*P(x,y)+3','false':1},
        row=dict(old_word=old_r7,new_word=new_g,old_expression=old_r7_formula,new_expression=g_formula,
                 parent_primitive_interval=[486,786],old_primitives=len(old_r7_flat),new_primitives=len(new_g_flat)),
        bundle=dict(old_word=canonical_word,new_word=new_bundle_word,old_expression=canonical,new_expression=new_bundle,
                    parent_primitive_interval=[bundle_start,bundle_end],old_primitives=len(old_bundle_flat),new_primitives=len(new_bundle_flat)),
        all_other_primitives_unchanged=True,old_leaves=len(old_flat),new_leaves=len(new_flat),
        complete_guarded_cfg=dict(independent_resolvers_agree=True,final_checks=nf,reference_checks=nr),
        macros=contracts,gate='if c=a or c=b then 0 else And(core_f(a,b,c),RV(a,b,c))',
        eight_logical_row_positions_retained=True,
        scope='All natural a,b,c; arbitrary prior top and stack; initially zero scratch registers. Structural symbolic expression equalities and complete source CFG checks; no numerical sampling. Logical calculus equivalence and binary runtime are separate certificates.')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','old_leaves','new_leaves','complete_guarded_cfg','gate')},indent=2))
if __name__=='__main__':main()
