import importlib.util
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('kernel', ROOT / 'code/full_normal.py')
k = importlib.util.module_from_spec(spec)
spec.loader.exec_module(k)
Z=['z']
def V(i): return ['v',i]
def S(t): return ['s',t]
def E(s,t): return ['=',s,t]
def I(c,a,h): return ['i',c,a,h]
def norm(t): return k.walk(t, lambda i,d: V(i))
def eqsym(t,p): return ['tr',V(0),t,p]

def evaluate(t, env):
    if t[0]=='v': return env[t[1]]
    if t[0]=='z': return 0
    if t[0]=='s': return 1+evaluate(t[1],env)
    count=evaluate(t[1],env)
    if count>100: raise OverflowError()
    value=evaluate(t[2],env)
    for _ in range(count):
        value=evaluate(t[3],[value]+env)
        if value>10000: raise OverflowError()
    return value

# The named-zero certificate and a case-at-zero proof using its premise.
zero_matrix = E(I(V(0), Z, V(2)), Z)
zero_exists = ['di',zero_matrix,Z,Z]
k.check({'variables':0,'context':[],'goal':['d',zero_matrix], 'proof':zero_exists})

# Outer parameters a,b with context a=b. Matrix E(x,y) is
# I(y,a;u.b)=I(y,x;u.0). At x=0 the case premise needs a=0 to prove b=0.
matrix=E(I(V(0),V(2),V(4)),I(V(0),V(1),Z))
goal=['d',matrix]
shifted_matrix=k.shift(goal)[1]
# Inside DE(w) then DI(z), context is [a=w, Q Zero(w,y), a=b].
w_zero=['qe',S(Z),['hyp',1],Z]
w_a=eqsym(V(2),['hyp',0])
a_zero=['tr',V(0),w_zero,w_a]
zero_b=['tr',V(0),['hyp',2],a_zero]
b_zero=eqsym(Z,zero_b)
case_inside=['di',shifted_matrix,V(0),b_zero]
case_proof=['de',goal,zero_exists,case_inside]
case_cert={'variables':2,'context':[E(V(0),V(1))],'goal':goal,'proof':case_proof}
k.check(case_cert)

# Nontrivial normalization examples, including the needed residual open iterator.
add=lambda a,b:I(a,b,S(V(0)))
mul=lambda a,b:I(a,Z,add(k.shift(b),V(0)))
num=lambda n: Z if n==0 else S(num(n-1))
assert norm(add(num(3),num(4)))==num(7)
assert norm(mul(num(3),num(4)))==num(12)
assert norm(I(V(0),Z,Z))==I(V(0),Z,Z)
assert norm(I(S(V(0)),Z,Z))==Z
assert norm(I(S(S(V(0))),V(1),S(V(0))))==S(S(I(V(0),V(1),S(V(0)))))

rng=random.Random(1729)
def random_term(depth,scope):
    choices=['z','s','i']+(['v'] if scope else [])
    tag=rng.choice(choices if depth else ['z']+(['v'] if scope else []))
    if tag=='v': return V(rng.randrange(scope))
    if tag=='z': return Z
    if tag=='s': return S(random_term(depth-1,scope))
    return I(random_term(depth-1,scope),random_term(depth-1,scope),random_term(depth-1,scope+1))

checked=0
for _ in range(1000):
    t=random_term(4,2)
    env=[rng.randrange(4),rng.randrange(4)]
    try:
        value=evaluate(t,env)
        nt=norm(t)
        assert nt==norm(nt)
        k.term(nt,2)
        assert evaluate(nt,env)==value
        assert norm(k.sub(t,num(2)))==k.sub(nt,num(2))
        checked+=1
    except OverflowError:
        pass

# Malformed or nonnormal certificates must not be accepted.
reject=[
 {'variables':0,'context':[],'goal':E(Z,S(Z)),'proof':Z},
 {'variables':0,'context':[],'goal':E(I(S(Z),Z,Z),Z),'proof':Z},
 {'variables':0,'context':[],'goal':E(Z,Z),'proof':['hyp',True]},
 {'variables':0,'context':[],'goal':E(Z,Z),'proof':V(0)},
]
for c in reject:
    try: k.check(c)
    except (ValueError,IndexError,TypeError,KeyError): pass
    else: raise AssertionError('accepted malformed certificate')
import json
(ROOT/'certificates/full_normal_case.json').write_text(json.dumps(case_cert,indent=2)+'\n')
print(json.dumps({'named_zero':True,'case_zero_with_used_hypothesis':True,'random_normalization_substitution_tests':checked,'rejection_tests':len(reject)}))
