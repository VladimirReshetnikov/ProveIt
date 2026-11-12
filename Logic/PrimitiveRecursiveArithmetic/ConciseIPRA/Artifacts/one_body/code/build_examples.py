"""Untrusted certificate builder for the raw one-body and clause control calculi."""
from pathlib import Path
import importlib.util
import json

ROOT=Path(__file__).resolve().parent

def module(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/(name+'.py'))
    m=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m

K=module('checker_one_body')
C=module('checker_clausal_control')

def S(x): return [0,x]
def I(n,a,h): return [n,a,h]
def eq(x,y): return [x,y]

def refl(t): return (eq(t,t), ['r',t])

def ev(p,q):
    s,t=p[0]
    b,r=q[0]
    c,a,h=b
    if c==0:
        assert a==s
        out=t
    else:
        assert c==S(c[1]) and I(c[1],a,h)==s
        out=K.opening(h,t)
    return (eq(r,out),['v',p[1],q[1]])

def join(p,q):
    assert p[0][0]==q[0][0]
    frame=I(0,p[0][0],0)
    return ev(p,ev(q,refl(frame)))

def sym(p): return join(refl(p[0][0]),p)
def trans(p,q):
    assert p[0][1]==q[0][0]
    return join(q,sym(p))

def zero(t):
    assert t[0]==0
    return ev(refl(t[1]),refl(t))

def succ(t):
    c,a,h=t
    assert c==S(c[1])
    return ev(refl(I(c[1],a,h)),refl(t))

def congruence(p,h):
    s,t=p[0]
    lower=I(0,s,h)
    upper=I(S(0),s,h)
    p0=zero(lower)
    first=ev(p0,refl(upper))
    second=ev(trans(p0,p),refl(upper))
    return join(second,first)

def use_body(index,body,witness,base):
    assert base[0]==K.opening(body,0)
    return (K.opening(body,witness),['u',index,witness,base[1]])

def recover_atomic(index,a):
    body=K.gate(a)
    zero_goal=K.opening(body,0)
    base=trans(zero(zero_goal[0]),sym(zero(zero_goal[1])))
    at_one=use_body(index,body,S(0),base)
    left=succ(at_one[0][0])
    right=succ(at_one[0][1])
    return trans(trans(sym(left),at_one),right)

def depth_refl(a,scope=0):
    if len(a)==2:
        assert a[0]==a[1]
        return refl(a[0])
    body=K.opening(a[0],S(0),1)
    target=K.opening(body,S(-scope-1))
    p=depth_refl(target,scope+1)
    return (a,['i',a,S(0),p[1]])

def induction(control=False):
    goal=[eq(I(1,0,S(1)),1)]
    z=-1
    assumption=eq(I(z,0,S(1)),z)
    if control:
        hypothesis=(assumption,['u',0,0,refl(0)[1]])
    else:
        hypothesis=recover_atomic(0,assumption)
    upper=I(S(z),0,S(1))
    step=trans(succ(upper),congruence(hypothesis,S(1)))
    assert step[0]==eq(upper,S(z))
    return (goal,['i',goal,0,step[1]])

def closed_use_of_induction(control=False):
    theorem=induction(control)
    # Opening the unused x chooses eigenparameter -1, leaving y unbound.
    body=K.opening(theorem[0][0],-1,1)
    base=zero(I(0,0,S(1)))
    goal=K.opening(body,S(S(0)))
    branch=['u',0,S(S(0)),base[1]]
    return (goal,['e',goal,theorem[1],branch])

def ungate_atomic(p):
    left=succ(p[0][0])
    right=succ(p[0][1])
    return trans(trans(sym(left),p),right)

def prove_gate_zero(a,scope):
    if len(a)==2:
        return trans(zero(a[0]),sym(zero(a[1])))
    body=K.opening(a[0],S(0),1)
    target=K.opening(body,S(-scope-1))
    branch=prove_gate_zero(target,scope+1)
    return (a,['i',a,S(0),branch[1]])

def nested_assumption_identity(control=False):
    # A is false in the standard model: D_xy(C(y,0,1)=0).
    # The closed theorem D_uv A is the conditional identity A -> A.
    # Therefore its branch must use, rather than ignore, its assumption.
    a=[eq(I(1,0,S(0)),0)]
    goal=[a]
    if control:
        branch=['u',0,0,refl(0)[1]]
    else:
        scope=1
        gate_body=K.gate(a)
        base=prove_gate_zero(K.opening(gate_body,0),scope)
        at_one=use_body(0,gate_body,S(0),base)
        b=-2
        closure_body=K.opening(at_one[0][0],b,1)
        plain_body=K.opening(a[0],b,1)
        plain_base=K.opening(plain_body,0)
        premise=recover_atomic(2,plain_base)
        transformed=congruence(premise,I(S(0),0,2))
        assert transformed[0]==K.opening(closure_body,0)
        step=use_body(1,closure_body,S(-3),transformed)
        plain_step=ungate_atomic(step)
        assert plain_step[0]==K.opening(plain_body,S(-3))
        introduction=['i',a,b,plain_step[1]]
        branch=['e',a,at_one[1],introduction]
    return (goal,['i',goal,0,branch])

def certificate(p): return {'goal':p[0],'proof':p[1]}

def write(name,p,control=False,accept=True):
    target=ROOT/'examples'/('control' if control else 'one_body')
    target.mkdir(parents=True,exist_ok=True)
    data=certificate(p) if isinstance(p,tuple) else p
    path=target/(name+'.json')
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    result=True
    try:
        (C if control else K).verify(data)
    except Exception:
        result=False
    assert result==accept,(name,result,accept)
    return {'file':str(path.relative_to(ROOT)),'accept':accept,'bytes':path.stat().st_size}

records=[]
for ctl in (False,True):
    records.append(write('reflexivity',refl(0),ctl))
    records.append(write('zero_computation',zero(I(0,S(0),S(1))),ctl))
    records.append(write('successor_computation',succ(I(S(0),0,S(1))),ctl))
    records.append(write('root_join_derived',join(refl(0),refl(0)),ctl))
    records.append(write('induction_uses_assumption',induction(ctl),ctl))
    records.append(write('elimination_uses_closure',closed_use_of_induction(ctl),ctl))
    records.append(write('nested_d_assumption_extraction',nested_assumption_identity(ctl),ctl))
    records.append(write('deep_reflexivity_derived',depth_refl([[[2,2]]]),ctl))
    records.append(write('reject_wrong_goal',{'goal':eq(0,S(0)),'proof':['r',0]},ctl,False))
    records.append(write('reject_boolean_term',{'goal':[True,True],'proof':['r',True]},ctl,False))
    records.append(write('reject_float_term',{'goal':[0.0,0.0],'proof':['r',0.0]},ctl,False))
    records.append(write('reject_unbound_index',{'goal':[1,1],'proof':['r',1]},ctl,False))
    records.append(write('reject_false_eval_source',{'goal':[0,S(0)],'proof':['v',['r',0],['r',I(0,S(0),0)]]},ctl,False))
    records.append(write('reject_capture',{'goal':[[1,1]],'proof':['i',[[1,1]],-1,['r',-1]]},ctl,False))
    records.append(write('reject_context_index',{'goal':[0,0],'proof':['u',0,0,['r',0]]},ctl,False))
    records.append(write('reject_extra_proof_field',{'goal':[0,0],'proof':['r',0,0]},ctl,False))
    records.append(write('reject_extra_input_field',{'goal':[0,0],'proof':['r',0],'extra':0},ctl,False))
(ROOT/'example_manifest.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({'examples':len(records),'positive':sum(r['accept'] for r in records),'total_bytes':sum(r['bytes'] for r in records)},indent=2))
