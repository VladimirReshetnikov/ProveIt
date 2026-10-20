#!/usr/bin/env python3
"""Independent binding of the literal223 source to its K_s arithmetic formula.

The comparator is a finite all-register source bisimulation. No finite runtime
sample is used. The postfix expression is executed symbolically, and each
optimized primitive macro is separately compared with the pinned Dag230 macro.
"""
from pathlib import Path
from functools import cache
import argparse, hashlib, json, re, sys

HERE=Path(__file__).resolve().parent
from audit_native_decoding import check as decode_sides


def freeze(x): return tuple(map(freeze,x)) if isinstance(x,list) else x
def h(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def seq(xs):
    assert xs
    result=xs[-1]
    for x in reversed(xs[:-1]): result=(x,result)
    return result


def chunks(t,lo,hi):
    ans=[]
    def visit(n,offset):
        end=offset+len(c.sites(n))
        if offset>=hi or end<=lo:return
        if lo<=offset and end<=hi:
            assert c.boundary(n)==(0,0,False)
            ans.append(n);return
        assert not c.leaf(n)
        visit(n[0],offset)
        visit(n[1],offset+len(c.sites(n[0])))
    visit(t,0);return ans


def execute(word):
    top='old_top';stack=['old_stack']
    for q in word:
        if q in (166,121,168,177):
            stack.append(top);top={166:'a',121:'b',168:'c',177:1}[q]
        elif q==218:top=('I',top,1)
        else:
            op={119:'I',181:'R',180:'Q',182:'E'}[q]
            top=(op,stack.pop(),top)
    assert stack==['old_stack','old_top']
    return top


def expected():
    I=lambda a,b:('I',a,b)
    Q=lambda a,b:('Q',a,b)
    R=lambda a,b:('R',a,b)
    E=lambda a,b:('E',a,b)
    N=lambda a:I(a,1)
    a,b,m='a','b','c'
    rel=R(b,m)
    subset=Q(m,I(R(m,a),R(m,b)))
    request=Q(b,I(m,N(Q(b,I(m,N(rel))))))
    U=Q(a,I(subset,request))
    H=Q(b,I(rel,N(Q(a,I(m,N(U))))))
    negated_core=Q(m,I(H,N(request)))
    rv=I(R(a,b),Q(m,R(a,b)))
    ev=I(E(a,b),Q(R(a,b),E(a,b)))
    # core=N(negated_core).  The released grammar emits
    # And(rv,And(ev,core)); the outer conjunction contributes N(core),
    # whose double negation is fused to negated_core itself.
    return N(I(rv,I(ev,negated_core)))


def main():
    global c
    ap=argparse.ArgumentParser()
    ap.add_argument('--baseline224-portable',type=Path,required=True,
                    help='Portable root extracted from the pinned K224 archive')
    ap.add_argument('--upstream225-portable',type=Path,required=True,
                    help='Portable root extracted from K224\'s nested pinned K225 archive')
    ap.add_argument('--source',type=Path,required=True)
    ap.add_argument('--grammar',type=Path,required=True)
    ap.add_argument('--macros',type=Path,default=HERE/'macro_data.json')
    ap.add_argument('--output',type=Path,default=HERE/'ks223_emitter_audit.json')
    args=ap.parse_args()
    base=args.baseline224_portable.resolve()
    up=args.upstream225_portable.resolve()/'baseline226'
    sys.path[:0]=[str(base/'verification'),str(up/'verification')]
    import reconstruct227 as c
    from local_bisimulation import check as compare
    grammar=json.loads(args.grammar.read_text())
    assert grammar['variant']=='seedrequest-s0-p0-r1-o120-hR'
    word=grammar['macro_word']
    expression=execute(word)
    assert expression==expected()==freeze(grammar['expression'])
    sides=decode_sides(expression)

    raw_path=up/'vendor/k230-rocq/coq/prog/Dag230.v'
    assert h(raw_path)=='7f44c6bc6cb2e5a7a30c1267738c8df7bfd8e036987721ac0bb6bdc326e54eaf'
    dag={int(q):(a,b) for q,a,b in re.findall(
        r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)',raw_path.read_text())}
    @cache
    def expand(q):
        def edge(s):
            if s=='EHalt':return ('CH',None)
            name,value=s.split();value=int(value)
            if name=='ENode':return expand(value)
            return ({'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC'}[name],value)
        return tuple(edge(x) for x in dag[q])

    data=json.loads(args.macros.read_text())
    macros={int(q):freeze(t) for q,t in data['macros'].items()}
    contracts={q:compare(expand(q),macros[q]) for q in sorted(set(word))}
    old_source=base/'machine/reference/sites.json'
    original=c.tree(json.loads(old_source.read_text()))
    actual=c.tree(json.loads(args.source.read_text()))
    path='11101001001110'
    old_ax=c.subtree(original,path);actual_ax=c.subtree(actual,path)
    prefix=chunks(old_ax,0,1893);suffix=chunks(old_ax,3970,4004)
    assert len(prefix)==6 and len(suffix)==2
    reference=seq(prefix+[macros[q] for q in word]+suffix)
    assert [r[1:] for r in c.sites(reference)]==[r[1:] for r in c.sites(actual_ax)]
    assert c.replace(actual,path,old_ax)==original, 'Source outside emitter changed'
    simulation=compare(reference,actual_ax)
    assert c.boundary(actual_ax)==(0,0,False)
    report=dict(status='INDEPENDENT_KS223_EMITTER_AND_NATIVE_DECODING_PASS',
                source_sha256=h(args.source),grammar_sha256=h(args.grammar),
                upstream_dag_sha256=h(raw_path),macro_data_sha256=h(args.macros),
                variant=grammar['variant'],
                macro_word=word,macro_count=len(word),expression=expression,
                formula='And(V_R,And(H_R,Exists_c(And(H,W)))) with the recorded fusions',
                exact_outside_emitter_unchanged=True,
                canonical_right_associated_reference_leaves=len(c.sites(reference)),
                macro_contracts=contracts,source_bisimulation=simulation,
                decoder_sideconditions=sides,
                scope='Literal source/emitter and uniform arithmetic decoding interface. The mathematical consistency proof, enumeration, blank startup and binary runtime are separate.')
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(status=report['status'],source_sha256=report['source_sha256'],
                         macro_count=len(word),macro_contracts=len(contracts),
                         bisimulation_boundaries=simulation['test_pairs'],
                         reference_leaves=report['canonical_right_associated_reference_leaves']),indent=2))


if __name__=='__main__':main()
