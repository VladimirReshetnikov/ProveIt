from motif_compiler import *
from pathlib import Path
import hashlib,time
OUT=Path(__file__).parent
stats=Counter(); examples={}

def test_candidate(p,rules):
    try:
        fs,_,_=expanded_oracle(p,rules); expected=True
    except ValueError: expected=False
    packet=make_packet(p,rules,validate=False)
    eq,vs=compile_schema(packet['schema'],rules,len(p.x));w=packet['witness']
    actual=all(type(x) is int and x>=0 for x in w.values()) and all(q.evaluate(w)==0 for _,q in eq)
    assert actual==expected,(p,expected,[(n,q.evaluate(w)) for n,q in eq if q.evaluate(w)])
    stats['candidate_plans']+=1;stats['legal_plans']+=expected
    if expected:
        assert packet['output']==ckey(fs[0]);stats['residuals_checked']+=len(eq)
    return packet if expected else None

# Exhaustive tiny simultaneous allocations, including object competition.
rules=[Rule('evolve','h',0,(0,1)),Rule('in','h',0,(0,1)),Rule('out','h',1,(1,0)),Rule('divide','h',0,(0,1),(1,0)),Rule('dissolve','h',1,(1,0)),Rule('evolve','skin',1,(1,0))]
for sx in product(range(3),repeat=2):
    for ax in product(range(3),repeat=2):
        for bx in product(range(2),repeat=2):
            cfg=Cfg('skin',sx,(Cfg('h',ax),Cfg('h',bx)))
            for p in enumerate_plans(cfg,rules):test_candidate(p,rules)

# Contextual counterexample: a token in one parent cannot serve another's child.
r=[Rule('in','h',0,(0,1))]
idle=Plan('h',(0,0));take=Plan('h',(0,0),mode=0)
p_good=Plan('skin',(0,0),(Plan('p',(1,0),(take,)),Plan('p',(0,0),(idle,))))
p_bad=Plan('skin',(0,0),(Plan('p',(1,0),(idle,)),Plan('p',(0,0),(take,))))
assert test_candidate(p_good,r);assert test_candidate(p_bad,r) is None
examples['separate_parent_contexts']=test_candidate(p_good,r)

# Source-profile uniformity fails: one of two identical empty children must receive.
p=Plan('skin',(1,0),(idle,take));examples['split_identical_children']=test_candidate(p,r)
assert test_candidate(Plan('skin',(1,0),(idle,idle)),r) is None
assert test_candidate(Plan('skin',(1,0),(take,take)),r) is None

# Same-step produced objects cannot be used by a sibling's incoming rule.
r=[Rule('dissolve','d',0,(0,1)),Rule('in','h',1,(1,0))]
p=Plan('skin',(0,0),(Plan('d',(1,0),mode=0),Plan('h',(0,0),mode=1)))
assert test_candidate(p,r) is None
p=Plan('skin',(0,0),(Plan('d',(1,0),mode=0),Plan('h',(0,0))))
examples['released_objects_are_not_old_resources']=test_candidate(p,r)

# Dissolution resources remain local even while two parents divide simultaneously.
r=[Rule('divide','p',0,(1,0,0),(1,0,0)),Rule('dissolve','d',1,(0,0,1))]
p=Plan('skin',(0,0,0),(Plan('p',(1,0,0),(Plan('d',(0,1,0),mode=1),),mode=0),Plan('p',(1,0,0),mode=0)))
q=test_candidate(p,r);examples['dissolution_then_contextual_copy']=q
fs,_,_=expanded_oracle(p,r)
assert Counter(c.x for c in fs[0].children)==Counter({(1,0,1):2,(1,0,0):2})

# Complete concurrent division along a chain, all integer data exact.
r=[Rule('divide','h',0,(1,),(1,))]
for depth in range(1,11):
    p=Plan('h',(1,),mode=0)
    for _ in range(depth-1):p=Plan('h',(1,),(p,),mode=0)
    p=Plan('skin',(0,),(p,));q=test_candidate(p,r)
    fs,_,_=expanded_oracle(p,r)
    def size(c):return 1+sum(size(x) for x in c.children)
    assert size(fs[0])==2**(depth+1)-1
    assert len(q['schema']['transitions'])==depth+1
    stats['exponential_family_max_membranes']=size(fs[0])
    if depth==10:examples['nested_division_depth10']=q

# Huge simultaneous population: 2^10000 identical leaves, one schema, no expansion.
N=2**10000;Z=(0,)
r=[Rule('divide','h',0,(1,),(1,))]
schema={'configs':[{'label':'h','children':[]},{'label':'skin','children':[0]},{'label':'skin','children':[0]}], 'transitions':[{'source':0,'children':[],'mode':0,'targets':[0,0]},{'source':1,'children':[0],'mode':-1,'targets':[2]}], 'root':1}
eq,vs=compile_schema(schema,r,1);w=dict.fromkeys(vs,0)
w.update({'x:0:0':1,'c:1:0':N-1,'c:2:0':2*N-1,'m:1:0':N-1,'f:0:0':2,'f:1:2':1})
assert all(p.evaluate(w)==0 for _,p in eq)
examples['huge_population']={'schema':schema,'ledger':{'variables':len(vs),'residuals':len(eq),'max_degree':2},'population_bits':N.bit_length(),'root_post_population_bits':(2*N).bit_length()}
stats['huge_population_bits']=N.bit_length()

# Aggregate mass cannot determine the next state, even with only division.
r=[Rule('divide','h',0,(0,1),(0,1))]
a=Plan('skin',(0,0),(Plan('h',(2,0),mode=0),Plan('h',(0,0))))
b=Plan('skin',(0,0),(Plan('h',(1,0),mode=0),Plan('h',(1,0),mode=0)))
fa,_,_=expanded_oracle(a,r);fb,_,_=expanded_oracle(b,r)
assert len(fa[0].children)==3 and len(fb[0].children)==4
examples['same_mass_different_successor']={'first':test_candidate(a,r),'second':test_candidate(b,r)}

# Every derived auxiliary mutation must be rejected at a valid point.
q=examples['nested_division_depth10'];eq,_=compile_schema(q['schema'],[Rule('divide','h',0,(1,),(1,))],1)
for name,value in q['witness'].items():
    if name.split(':')[0] not in ('u','y','o','f'):continue
    for delta in (-1,1):
        if value+delta<0:continue
        w=q['witness'].copy();w[name]+=delta
        assert any(p.evaluate(w) for _,p in eq);stats['auxiliary_mutations_rejected']+=1

stats['examples']=len(examples)
(OUT/'examples.json').write_text(json.dumps(examples,indent=2)+'\n')
receipt={'status':'passed','checks':dict(stats),'scope':'Finite exact checks of weak-division motif quadratic compiler, not formal verification or universal frontend certification.'}
(OUT/'replay_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))

# A fixed deterministic four-rule system forces exponentially many distinct motifs.
r=[Rule('evolve','h',0,(2,0,0,0)),Rule('evolve','h',2,(0,1,0,0)),Rule('evolve','h',3,(1,1,0,0)),Rule('divide','h',1,(0,0,1,0),(0,0,0,1))]
leaves=[Cfg('h',(0,1,0,0))]
for t in range(1,9):
    children=tuple(Plan('h',c.x,evolution=((0,c.x[0]),) if c.x[0] else (),mode=3) for c in leaves)
    p=Plan('skin',(0,0,0,0),children);fs,_,_=expanded_oracle(p,r)
    children=tuple(Plan('h',c.x,evolution=tuple((ri,c.x[r[ri].a]) for ri in (0,1,2) if c.x[r[ri].a])) for c in fs[0].children)
    p=Plan('skin',(0,0,0,0),children);fs,_,_=expanded_oracle(p,r);leaves=list(fs[0].children)
    expected={sum(bit*4**i for i,bit in enumerate(bits)) for bits in product((0,1),repeat=t)}
    assert len(leaves)==2**t and {c.x[0] for c in leaves}==expected
    assert all(c.x[1:]==(1,0,0) for c in leaves)
    stats['deterministic_separation_rounds']+=1
stats['deterministic_distinct_leaf_motifs']=len(leaves)
receipt['checks']=dict(stats)
(OUT/'replay_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('Extended deterministic anti-sharing checks passed:',len(leaves),'distinct motifs')
