"""Independent semantic checks of clausal opening and capture boundaries."""
import importlib.util
import hashlib
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parent
PATH = ROOT/'checker.py'
spec=importlib.util.spec_from_file_location('clausal',PATH)
k=importlib.util.module_from_spec(spec)
spec.loader.exec_module(k)
rng=random.Random(20261111)


def value(a,free,bound):
    if type(a) is int:
        return 0 if a==0 else free[-a-1] if a<0 else bound[-a]
    if a[0]=='s':
        return value(a[1],free,bound)+1
    count=value(a[1],free,bound)
    r=value(a[2],free,bound)
    for _ in range(count):
        r=value(a[3],free,bound+[r])
    return r


def tree(depth, fuel):
    variables=[0,-1,-2]+list(range(1,depth+1))
    if fuel==0 or rng.random()<0.4:
        return rng.choice(variables)
    if rng.random()<0.4:
        return ['s',tree(depth,fuel-1)]
    # Small fixed counters keep the independent arithmetic evaluation bounded.
    counter=rng.choice([['s',0],['s',['s',0]],-1])
    return ['i',counter,tree(depth,fuel-1),tree(depth+1,fuel-1)]

checks=0
for depth in range(3):
    for _ in range(700):
        a=tree(depth+1,4)
        image=tree(0,3)
        assert k.term(a,2,depth+1)
        assert k.term(image,2,0)
        out=k.opening(a,image,depth)
        assert k.term(out,2,depth)
        free=[rng.randrange(3),rng.randrange(3)]
        locals=[rng.randrange(3) for _ in range(depth)]
        expected=value(a,free,[value(image,free,[])]+locals)
        got=value(out,free,locals)
        assert got==expected,(a,image,depth,out,free,locals,got,expected)
        checks+=1

# Explicit reductions exposed below retained binders and replacement images
# whose own iterator body binds a positive index.
image=['i',['s',0],-1,1]
a=['i',['s',0],1,['i',2,1,['s',1]]]
out=k.opening(a,image)
assert k.term(out,1)
for n in range(4):
    assert value(out,[n],[])==value(a,[n],[value(image,[n],[])])
    checks+=1
assert k.opening(['i',2,1,['s',1]],0,1)==1

R=lambda a:['r',a]
truth=['=',0,0]
Dtruth=['d',truth]
trivial=['i',Dtruth,0,R(0)]
negative={
 'bool_goal':{'goal':['=',False,False],'proof':R(0)},
 'free_goal':{'goal':['=',-1,-1],'proof':R(0)},
 'positive_free_goal':{'goal':['=',1,1],'proof':R(0)},
 'canonical_zero_goal':{'goal':['=',['i',0,0,1],0],'proof':R(0)},
 'de_escape':{'goal':['=',-1,-1],'proof':['e',['=',-1,-1],trivial,R(-1)]},
 'di_future_variable':{'goal':Dtruth,'proof':['i',Dtruth,0,R(-2)]},
 'di_wrong_target':{'goal':Dtruth,'proof':['i',Dtruth,0,R(-1)]},
 'bound_witness':{'goal':Dtruth,'proof':['i',Dtruth,1,R(0)]},
 'boolean_use_index':{'goal':Dtruth,'proof':['i',Dtruth,0,['u',False,0,R(0)]]},
 'unknown_tag':{'goal':truth,'proof':['magic']},
 'extra_key':{'goal':truth,'proof':R(0),'free':1},
 'false_step':{'goal':truth,'proof':['x',R(0),R(['s',0])]},
 'wrong_step_previous':{'goal':truth,'proof':['x',R(['s',0]),R(['i',['s',0],0,1])]},
}
for name,c in negative.items():
    try:k.verify(c)
    except Exception:pass
    else:raise AssertionError(('accepted invalid',name))
assert k.verify({'goal':Dtruth,'proof':trivial})
report={'reviewed_source':str(PATH),'source_sha256':hashlib.sha256(PATH.read_bytes()).hexdigest(),'semantic_opening_checks':checks,'targeted_negative_certificates':len(negative),
        'positive_smoke_checks':1,'source_review':'No flaw found',
        'scope_explanation':'Substitution images have no free positive indices; their internal positive indices remain bound internally. Fresh eigenvariables use negative free levels, validated at current scope.',
        'limitations':'Finite evaluation tests supplement the structural substitution proof; they do not establish universal arithmetic or logical soundness.'}
(ROOT/'clausal_review.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
