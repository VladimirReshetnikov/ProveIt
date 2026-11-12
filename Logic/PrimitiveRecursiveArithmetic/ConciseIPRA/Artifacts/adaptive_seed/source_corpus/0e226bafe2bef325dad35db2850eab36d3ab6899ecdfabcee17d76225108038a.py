#!/usr/bin/env python3
"""Check symbolic equational certificates for the reset-gate compiler.

This is a small checker for the displayed equational fragment, not a
formalization of first-order iPRA or a candidate for the checker frontier.
M and R are named *fixed* instances of zero-initialized scalar iteration:
M(n,a)=J(n;u.a), R(n)=J(n;u.T(u)). Their four equations below are direct
instances of J0/JS. The correspondence of these abbreviations with the
staged source grammar is stated here, rather than encoded in this checker.
The only nondefinitional numerical axiom is B(Sa,b)=a, plus those J instances.
The induction rule checks a literal-equation base and successor instance,
with at most that equation as an additional local assumption.
"""
from __future__ import annotations
import json
from dataclasses import dataclass
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run this certificate verifier without Python -O")

Term = tuple

def f(name, *args): return (name, *args)
def v(name): return ("$" + name,)
def p(name): return ("?" + name,)
Z=f("0")
def S(a): return f("S",a)
ONE=S(Z)

def subst(t, env):
    if t[0].startswith("?"): return env.get(t[0],t)
    return (t[0], *(subst(x,env) for x in t[1:]))

def match(pattern, term, env=None):
    env={} if env is None else env
    if pattern[0].startswith("?"):
        k=pattern[0]
        if k in env and env[k]!=term: return None
        env[k]=term
        return env
    if pattern[0]!=term[0] or len(pattern)!=len(term): return None
    for a,b in zip(pattern[1:],term[1:]):
        if match(a,b,env) is None: return None
    return env

def at(t,path):
    for i in path: t=t[i+1]
    return t

def replace(t,path,u):
    if not path: return u
    i=path[0]+1
    q=list(t); q[i]=replace(q[i],path[1:],u)
    return tuple(q)

def paths(t):
    yield ()
    for i,x in enumerate(t[1:]):
        for q in paths(x): yield (i,*q)

def free(t):
    if t[0].startswith("$"): return {t[0]}
    ans=set()
    for x in t[1:]: ans.update(free(x))
    return ans

@dataclass(frozen=True)
class Rule:
    lhs:Term
    rhs:Term
    deps:frozenset=frozenset()

rules={}
certificates=[]
x,y,n,a,b=p('x'),p('y'),p('n'),p('a'),p('b')
A=v('a')
H=lambda t:f('h',t)
B=lambda x,y:f('B',x,y)
F=lambda x:f('F',x)
M=lambda n,a:f('M',n,a)
sg=lambda x:f('sigma',x)
ze=lambda x:f('Z',x)
d=lambda x,y:f('d',x,y)
C=lambda n,a,b:f('C',n,a,b)
T=lambda x:f('T',x)
R=lambda x:f('R',x)
V=lambda x:f('V',x)
I=lambda x:f('I',x)

def primitive(name,l,r,kind):
    rules[name]=Rule(l,r)
    certificates.append({'kind':kind,'name':name,'lhs':l,'rhs':r})

primitive('B',B(S(x),y),x,'axiom')
primitive('successor',B(Z,x),S(x),'definition')
primitive('M0',M(Z,a),Z,'J0-instance')
primitive('MS',M(S(n),a),a,'JS-instance')
primitive('R0',R(Z),Z,'J0-instance')
primitive('RS',R(S(n)),T(R(n)),'JS-instance')
for name,l,r in [
    ('F',F(x),B(x,Z)),
    ('sigma',sg(x),M(x,ONE)),
    ('Z',ze(x),F(sg(x))),
    ('C',C(n,a,b),F(B(M(ze(n),S(S(a))),b))),
    ('T',T(x),B(M(ze(x),S(S(A))),H(F(x)))),
    ('V',V(n),R(S(n))),
    ('I',I(n),F(V(n))),
]: primitive(name,l,r,'definition')

# Prefer semantic endpoint lemmas before unfolding abbreviations.
trusted=dict(rules)
priority=['B','successor','M0','MS','R0','RS']

def replay(start, steps):
    t=start; deps=set()
    for step in steps:
        rule=rules[step['rule']]
        lhs,rhs=(rule.rhs,rule.lhs) if step.get('reverse',False) else (rule.lhs,rule.rhs)
        env={k:tuplify(z) for k,z in step.get('extra',{}).items()}
        env=match(lhs,at(t,tuple(step['path'])),env)
        assert env is not None, ('rule does not match',step,t)
        out=subst(rhs,env)
        assert {q[0] for q in subtree(out) if q[0].startswith('?')} <= ({q[0] for q in subtree(at(t,tuple(step['path']))) if q[0].startswith('?')} | {q[0] for z in env.values() for q in subtree(z) if q[0].startswith('?')}), ('uninstantiated',step,out)
        t=replace(t,tuple(step['path']),out)
        deps.update(rule.deps)
    return t,frozenset(deps)

def tuplify(x): return tuple(tuplify(a) if isinstance(a,list) else a for a in x)
def subtree(t):
    yield t
    for x in t[1:]: yield from subtree(x)

def one(t,name,path=(),reverse=False,extra=None):
    q={'rule':name,'path':list(path)}
    if reverse: q['reverse']=True
    if extra: q['extra']=extra
    r,deps=replay(t,[q])
    return r,[q],deps

def normalize(t,limit=10000):
    start=t; steps=[]
    ordered=priority+[q for q in rules if q not in priority and not q.startswith('IH')]
    for _ in range(limit):
        found=False
        # outermost rewrite, then restart
        for path in paths(t):
            for name in ordered:
                rule=rules[name]
                if rule.deps: continue
                env=match(rule.lhs,at(t,path),{})
                if env is None: continue
                u=subst(rule.rhs,env)
                if u==at(t,path): continue
                t=replace(t,path,u)
                steps.append({'rule':name,'path':list(path)})
                found=True;break
            if found:break
        if not found:
            assert replay(start,steps)[0]==t
            return t,steps
    raise AssertionError('normalization limit')

def certify(name,l,r,left=None,right=None,expected_deps=frozenset(),generalize=True):
    if left is None: lnf,left=normalize(l)
    else: lnf,_=replay(l,left)
    if right is None: rnf,right=normalize(r)
    else: rnf,_=replay(r,right)
    ll,ld=replay(l,left);rr,rd=replay(r,right)
    assert ll==rr,(name,ll,rr)
    deps=ld|rd
    assert deps<=expected_deps,(name,deps,expected_deps)
    rules[name]=Rule(l,r,deps)
    certificates.append({'kind':'equation','name':name,'lhs':l,'rhs':r,'left':left,'right':right,'deps':sorted(deps)})
    return name

def induction(name,variable,l,r,base,step,hyp=None):
    def repl(t,old,new):
        if t==old:return new
        return (t[0],*(repl(c,old,new) for c in t[1:]))
    rb,rs=rules[base],rules[step]
    assert (rb.lhs,rb.rhs)==(repl(l,variable,Z),repl(r,variable,Z))
    assert (rs.lhs,rs.rhs)==(repl(l,variable,S(variable)),repl(r,variable,S(variable)))
    assert not rb.deps
    assert rs.deps<=({hyp} if hyp else set())
    # Only the designated equation hypothesis may depend on the eigenvariable.
    if hyp:
        rh=rules[hyp]
        assert (rh.lhs,rh.rhs)==(l,r)
    rules[name]=Rule(l,r)
    certificates.append({'kind':'EI','name':name,'variable':variable,'lhs':l,'rhs':r,'base':base,'step':step,'hypothesis':hyp})

for name,l,r in [
    ('F0',F(Z),ONE),('FS',F(S(x)),x),
    ('sigma0',sg(Z),Z),('sigmaS',sg(S(n)),ONE),
    ('Z0',ze(Z),ONE),('ZS',ze(S(n)),Z),
    ('C0',C(Z,a,b),a),('CS',C(S(n),a,b),b),
    ('T0',T(Z),S(A)),('TS',T(S(x)),S(H(x))),
    ('V0',V(Z),S(A)),
]:
    certify(name,l,r)
    priority.insert(0,name)

# Derive V(Sn)=T(V(n)) by a fixed finite expansion/folding chain.
N=v('n')
l=V(S(N));steps=[]
u,s,_=one(l,'V');steps+=s
u,s,_=one(u,'RS');steps+=s
u,s,_=one(u,'V',path=(0,),reverse=True);steps+=s
assert u==T(V(N))
certify('VS_fixed',l,T(V(N)),left=steps,right=[])
rules['VS']=Rule(V(S(n)),T(V(n)))
certificates.append({'kind':'parameter-generalization','name':'VS','source':'VS_fixed','variable':N,'metavariable':n})
priority.insert(0,'VS')

# Equation induction invariant. Reverse the local equation at one occurrence;
# this is an ordinary equality-replacement step, not an induction shortcut.
inv_l=S(F(V(N)));inv_r=V(N)
certify('invariant_base',S(F(V(Z))),V(Z))
rules['IH_state']=Rule(inv_l,inv_r,frozenset({'IH_state'}))
certificates.append({'kind':'assumption','name':'IH_state','lhs':inv_l,'rhs':inv_r})
start=V(S(N));u=start;st=[]
for name,path,rev in [('VS',(),False),('IH_state',(0,),True),('TS',(),False)]:
    u,s,_=one(u,name,path,rev);st+=s
assert u==S(H(F(V(N))))
certify('step_shape',start,u,left=st,right=[],expected_deps=frozenset({'IH_state'}))
# Both sides of the successor invariant reduce to this successor code.
lhs=S(F(V(S(N))));rhs=V(S(N))
ls=[{'rule':'step_shape','path':[0,0]},{'rule':'FS','path':[0]}]
rs=[{'rule':'step_shape','path':[]}]
certify('invariant_step',lhs,rhs,left=ls,right=rs,expected_deps=frozenset({'IH_state'}))
induction('invariant_fixed',N,inv_l,inv_r,'invariant_base','invariant_step','IH_state')
rules['invariant']=Rule(S(F(V(n))),V(n))
certificates.append({'kind':'parameter-generalization','name':'invariant','source':'invariant_fixed','variable':N,'metavariable':n})

# Base and successor computations of the compiled iterator.
certify('compiled_zero',I(Z),A)
start=I(S(N));u=start;st=[]
for name,path,rev in [('I',(),False),('VS',(0,),False),('invariant',(0,0),True),('TS',(0,),False),('FS',(),False),('I',(0,),True)]:
    u,s,_=one(u,name,path,rev);st+=s
assert u==H(I(N))
certify('compiled_successor',start,H(I(N)),left=st,right=[])

# Negative control: a false successor equation must not have equal normal forms.
left,_=normalize(I(Z));right,_=normalize(S(A))
assert left!=right


def replace_free(t,old,new):
    if t==old: return new
    return (t[0],*(replace_free(c,old,new) for c in t[1:]))

def check_receipt(records):
    """Replay serialized proof instructions without using normalization/search."""
    global rules
    previous=rules
    rules={}
    try:
        for item in records:
            kind=item['kind'];name=item['name']
            assert name not in rules, ('duplicate name',name)
            if kind in {'axiom','definition','J0-instance','JS-instance'}:
                assert name in trusted, ('unknown primitive',name)
                l,r=tuplify(item['lhs']),tuplify(item['rhs'])
                assert (l,r)==(trusted[name].lhs,trusted[name].rhs)
                rules[name]=trusted[name]
            elif kind=='assumption':
                rules[name]=Rule(tuplify(item['lhs']),tuplify(item['rhs']),frozenset({name}))
            elif kind=='equation':
                l,r=tuplify(item['lhs']),tuplify(item['rhs'])
                ln,ld=replay(l,item['left']);rn,rd=replay(r,item['right'])
                assert ln==rn, ('different endpoints',name)
                deps=ld|rd
                assert deps==frozenset(item['deps'])
                rules[name]=Rule(l,r,deps)
            elif kind=='EI':
                var=tuplify(item['variable'])
                assert len(var)==1 and var[0].startswith('$')
                l,r=tuplify(item['lhs']),tuplify(item['rhs'])
                base,step=rules[item['base']],rules[item['step']]
                assert not base.deps
                assert (base.lhs,base.rhs)==(replace_free(l,var,Z),replace_free(r,var,Z))
                assert (step.lhs,step.rhs)==(replace_free(l,var,S(var)),replace_free(r,var,S(var)))
                hyp=item['hypothesis']
                if hyp:
                    h=rules[hyp]
                    assert (h.lhs,h.rhs,h.deps)==(l,r,frozenset({hyp}))
                assert step.deps<=({hyp} if hyp else set())
                rules[name]=Rule(l,r)
            elif kind=='parameter-generalization':
                src=rules[item['source']]
                assert not src.deps
                var,meta=tuplify(item['variable']),tuplify(item['metavariable'])
                assert len(var)==len(meta)==1 and var[0].startswith('$') and meta[0].startswith('?')
                assert all(var[0] not in free(q.lhs)|free(q.rhs) for q in trusted.values())
                rules[name]=Rule(replace_free(src.lhs,var,meta),replace_free(src.rhs,var,meta))
            else: raise AssertionError(('unknown instruction',kind))
        expected={
            'C0':(C(Z,a,b),a),
            'CS':(C(S(n),a,b),b),
            'invariant':(S(F(V(n))),V(n)),
            'compiled_zero':(I(Z),A),
            'compiled_successor':(I(S(N)),H(I(N))),
        }
        for name,(l,r) in expected.items():
            q=rules[name]
            assert (q.lhs,q.rhs,q.deps)==(l,r,frozenset())
        return True
    finally:
        rules=previous

# Replay precisely the JSON-compatible data that will be delivered.
serialized=json.loads(json.dumps(certificates))
assert check_receipt(serialized)
rejected=0
for index,record in enumerate(serialized):
    if record['kind']!='equation': continue
    corrupt=json.loads(json.dumps(serialized))
    corrupt[index]['rhs']=['S',corrupt[index]['rhs']]
    try:
        check_receipt(corrupt)
    except (AssertionError,KeyError,TypeError,IndexError):
        rejected+=1
    else:
        raise AssertionError(('accepted corrupted equation',record['name']))

out={'status':'PASS','equations':sum(c['kind']=='equation' for c in certificates),
     'equation_inductions':sum(c['kind']=='EI' for c in certificates),
     'independent_serialized_replay':True,'corrupted_equations_rejected':rejected,
     'primitive_axioms':['B','M0','MS','R0','RS'],
     'scope':'The exact finite equational fragment above; not a full first-order formalization.',
     'claims':['C(0,a,b)=a','C(Sn,a,b)=b',
               'S(F(V(n)))=V(n)','I(0,a)=a','I(Sn,a)=h(I(n,a))'],
     'certificates':certificates}
(Path(__file__).resolve().parents[1] / 'certificates' / 'reset_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='certificates'},indent=2))
