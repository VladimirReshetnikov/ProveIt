"""Independent finite semantic audit of the separately authored PSC checker."""
from itertools import product
import importlib.util
import json
from pathlib import Path
import random
import sys

path=Path(__file__).resolve().parents[1] / 'reference_checker' / 'psc_hilbert.py'
spec=importlib.util.spec_from_file_location('psc_reviewed',path)
m=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=m
spec.loader.exec_module(m)
rng=random.Random(16491)
names=('x','y','z','_v0','_v1')


def random_formula(depth):
    choice=rng.randrange(4) if depth else rng.randrange(2)
    if choice==0:
        return m.BOTTOM
    if choice==1:
        return m.Rel(m.Var(rng.choice(names)),m.Var(rng.choice(names)))
    if choice==2:
        return m.Imp(random_formula(depth-1),random_formula(depth-1))
    return m.All(m.Var(rng.choice(names)),random_formula(depth-1))


def parse(tokens):
    def read(i):
        op=tokens[i]
        if op=='B':
            return ('bottom',),i+1
        if op=='R':
            return ('atom',tokens[i+1],tokens[i+2]),i+3
        if op=='I':
            a,j=read(i+1)
            b,k=read(j)
            return ('imp',a,b),k
        assert op=='A'
        a,j=read(i+2)
        return ('all',tokens[i+1],a),j
    tree,end=read(0)
    assert end==len(tokens)
    return tree


def evaluate(tree,env,relation):
    tag=tree[0]
    if tag=='bottom':return False
    if tag=='atom':return (env[tree[1]],env[tree[2]]) in relation
    if tag=='imp':return not evaluate(tree[1],env,relation) or evaluate(tree[2],env,relation)
    return all(evaluate(tree[2],env|{tree[1]:v},relation) for v in (0,1))


def relation(mask):
    return {p for i,p in enumerate(product((0,1),repeat=2)) if mask>>i&1}


counts={'simultaneous_substitution_semantics':0,'UI_semantics':0,
        'PSC_independent_semantics':0,'malformed_byte_total_rejections':0}
for i in range(600):
    formula=random_formula(5)
    tree=parse(formula.tokens)
    mapping={v:rng.choice(names) for v in rng.sample(names,rng.randrange(6))}
    replaced=m.substitute_many(formula,mapping)
    replaced_tree=parse(replaced.tokens)
    ui=m.check_certificate([{'op':'UI','x':rng.choice(names),
                            'A':list(formula.tokens),'y':rng.choice(names)}]).conclusion
    uitree=parse(ui.tokens)
    for _ in range(16):
        env={v:rng.randrange(2) for v in names}
        rel=relation(rng.randrange(16))
        changed=env|{v:env[w] for v,w in mapping.items()}
        assert evaluate(replaced_tree,env,rel)==evaluate(tree,changed,rel),(formula,mapping,replaced)
        assert evaluate(uitree,env,rel),(formula,ui)
        counts['simultaneous_substitution_semantics']+=1
        counts['UI_semantics']+=1


def direct_psc(tree,params,env,rel):
    if params:
        return all(direct_psc(tree,params[1:],env|{params[0]:v},rel) for v in (0,1))
    rho=lambda x,y:evaluate(tree,env|{'x':x,'y':y},rel)
    sub=lambda x,a:all((z,x) not in rel or (z,a) in rel for z in (0,1))
    sb=all(any(all(not rho(x,y) or sub(y,b) for y in (0,1)) for b in (0,1)) for x in (0,1))
    if not sb:return True
    def closed(seed,hull):
        closure=all(not ((sub(x,seed) or (x,hull) in rel) and rho(x,y)) or (y,hull) in rel
                    for x,y in product((0,1),repeat=2))
        support=all((y,hull) not in rel or any(rho(x,y) for x in (0,1)) for y in (0,1))
        return closure and support
    return all(any(closed(seed,hull) for hull in (0,1)) for seed in (0,1))


for i in range(80):
    formula=random_formula(4)
    tree=parse(formula.tokens)
    psc=m.psc_instance(formula,m.Var('x'),m.Var('y'))
    psctree=parse(psc.tokens)
    # The independent direct check universally closes all three remaining names;
    # closing an absent variable is harmless in this nonempty domain.
    for mask in range(16):
        rel=relation(mask)
        direct=direct_psc(tree,['z','_v0','_v1'],{'x':0,'y':0},rel)
        computed=evaluate(psctree,{},rel)
        assert direct==computed,(formula,mask,psc,direct,computed)
        counts['PSC_independent_semantics']+=1


for i in range(10000):
    malformed=bytes(rng.randrange(256) for _ in range(rng.randrange(80)))
    result=m.refutes_bytes(malformed)
    assert result is False,malformed
    counts['malformed_byte_total_rejections']+=1

# Fixed Python decimal-conversion cap is bypassed by the checker's parser.
huge=b'[{"op":"GEN","line":'+b'9'*10000+b',"x":"x"}]'
assert m.refutes_bytes(huge) is False
counts['very_large_integer_rejection']=1

print(json.dumps(counts,indent=2,sort_keys=True))
