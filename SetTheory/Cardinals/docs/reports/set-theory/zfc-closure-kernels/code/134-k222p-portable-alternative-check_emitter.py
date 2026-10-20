"""Independent expression, primitive-word, and complete CFG binding for conditional G222."""
from pathlib import Path
from functools import cache
import sys,json,hashlib,re,zipfile,io
HERE=Path(__file__).resolve().parent
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--inputs',type=Path,required=True);ap.add_argument('--results',type=Path,required=True);ap.add_argument('--baseline-archive',type=Path,required=True);args=ap.parse_args()
sys.path.insert(0,str(HERE/'helpers'))
import seed_tools as b
from local_bisimulation import check as bisimulation
s=b.s
out=args.results
base=args.inputs
sha=lambda raw:hashlib.sha256(raw).hexdigest()
table=b.read_table((base/'parent.k.tm').read_bytes())
parent=s.tree(json.loads((base/'parent_sites.json').read_text()))
final=s.tree(json.loads((out/'sites.json').read_text()))
assert sha((base/'parent_sites.json').read_bytes())=='b4e453a8801597124fd9b3ee1cd2db1cdf80c0bd904c2ffb59b79d95e91a6e96'
groups,_=b.decoder_map(table,parent)
q=lambda k:b.sole(groups,k)
flat=lambda t:tuple((o,v) for p,o,v in s.sites(t))
I=lambda a,b:('I',a,b)
Q=lambda a,b:('Q',a,b)
R=lambda a,b:('R',a,b)
E=lambda a,b:('E',a,b)
N=lambda a:I(a,1)
a,bb,c='a','b','c'
member=R(bb,c)
subset=Q(c,I(R(c,a),R(c,bb)))
request=Q(bb,I(c,N(Q(bb,I(c,N(member))))))
closure=Q(a,I(subset,request))
hereditary=Q(bb,I(member,N(Q(a,I(c,N(closure))))))
core=I(c,N(Q(c,I(member,N(hereditary)))))
rv=I(R(a,bb),Q(c,R(a,bb)))
helper=I(E(a,bb),Q(R(a,bb),E(a,bb)))
old_bundle=N(I(core,I(rv,N(helper))))
new_bundle=N(I(core,N(rv)))
old_r7=I(E(c,a),I(E(c,bb),E(a,bb)))
new_g=I(E(c,a),I(E(c,bb),Q(R(a,bb),E(a,bb))))
def word(e):
    if isinstance(e,(str,int)):return [{a:166,bb:121,c:168,1:177}[e]]
    if e[0]=='I' and e[2]==1:return word(e[1])+[218]
    return word(e[1])+word(e[2])+[{'I':119,'Q':180,'R':181,'E':182}[e[0]]]
macros={166:q(98),121:q(12),168:q(166),177:q(184)[0],119:q(90),180:q(86),
        181:(q(90),('CI',1)),182:(q(86),('CI',1)),218:q(184)}
wf=lambda w:sum((flat(macros[k]) for k in w),())
for expr in (old_bundle,new_bundle,old_r7,new_g):assert b.execute_word(word(expr))==expr
assert len(word(old_bundle))==71
pf,ff=flat(parent),flat(final)
assert pf[486:786]==wf(word(old_r7))
assert pf[2541:4618]==wf(word(old_bundle))
expected=pf[:486]+wf(word(new_g))+pf[786:2541]+wf(word(new_bundle))+pf[4618:]
assert expected==ff
assert len(ff)==4581 and len(pf)==4799

# The changed source is a complete CFG equivalent of a direct closed-macro
# reference. All unchanged blocks, gates, and control exits remain literal.
def seq(parts):
    assert parts
    return parts[0] if len(parts)==1 else (parts[0],seq(parts[1:]))
def replace(n,changes):
    if n in changes:return changes[n]
    return n if s.leaf(n) else tuple(replace(v,changes) for v in n)
pc,rel,eq,all_,imp,neg=(q(k) for k in [166,155,182,86,90,184])
factors_g=[q(99),rel,eq,all_,q(205)]
gate=q(116)[1][1][1]
factors_bundle=[pc,rel,q(153),neg,imp,neg,gate,q(193)]
assert q(207)==((q(99),eq),q(205))
assert q(153)==(all_,imp)
assert all(s.boundary(v)==(0,0,False) for v in factors_g+factors_bundle)
reference=replace(parent,{q(207):seq(factors_g),q(224):seq(factors_bundle)})
assert flat(reference)==ff
gf,nf=s.graph_arithmetic(s.sites(final));gr,nr=s.graph_arithmetic(s.sites(reference))
assert gf==gr==s.graph_intervals(s.sites(final))==s.graph_intervals(s.sites(reference))

# Independently link every macro to pinned K230 programs using finite
# all-register bisimulation; no bounded numerical samples.
archive=args.baseline_archive
assert sha(archive.read_bytes())=='cf5db8d08a34f5661ad1266226809ed1f0099fd38374c66d127e1e06519c6887'
with zipfile.ZipFile(archive) as z:
    nested=z.read('K224_Construction_2026-10-20/portable/vendor/K225_Construction_2026-10-19.zip')
with zipfile.ZipFile(io.BytesIO(nested)) as z:
    dag=z.read('K225_Construction_2026-10-19/portable/baseline226/vendor/k230-rocq/coq/prog/Dag230.v')
assert sha(dag)=='7f44c6bc6cb2e5a7a30c1267738c8df7bfd8e036987721ac0bb6bdc326e54eaf'
nodes={int(k):(u,v) for k,u,v in re.findall(r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)',dag.decode())}
@cache
def expand(k):
    def edge(e):
        if e=='EHalt':return 'CH',None
        kind,arg=e.split();arg=int(arg)
        if kind=='ENode':return expand(arg)
        return {'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC'}[kind],arg
    return tuple(edge(e) for e in nodes[k])
contracts={k:bisimulation(expand(k),m) for k,m in macros.items()}
receipt=dict(status='EXACT_CONDITIONAL_G_EMITTER_AND_SOURCE_PASS',
    source_sha256=sha((out/'sites.json').read_bytes()),
    conditional_parent_sha256=sha((base/'parent_sites.json').read_bytes()),
    parent_bundle_word=word(old_bundle),bundle_word=word(new_bundle),
    parent_bundle_expression=old_bundle,bundle_expression=new_bundle,
    parent_equality_word=word(old_r7),equality_word=word(new_g),equality_expression=new_g,
    parent_r7_interval=[486,786],parent_bundle_interval=[2541,4618],
    all_other_primitives_unchanged=True,parent_leaves=len(pf),new_leaves=len(ff),
    independent_guarded_CFG_resolvers_agree=True,guarded_cases=nf,reference_cases=nr,
    macro_contracts=contracts,upstream_Dag230_sha256=sha(dag),
    scope='All natural a,b,c and arbitrary prior top/stack, with initially clean scratch. Exact G row and And(conditional_K,RV), unchanged gate and enumerator. Calibration and binary runtime are separate obligations.')
(out/'emitter222.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ('parent_bundle_word','bundle_word','parent_bundle_expression','bundle_expression','macro_contracts')},indent=2))
