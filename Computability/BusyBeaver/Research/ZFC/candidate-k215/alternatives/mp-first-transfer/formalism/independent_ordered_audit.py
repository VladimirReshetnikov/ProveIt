#!/usr/bin/env python3
"""Independent certificate reader; imports neither generator nor inherited kernel."""
import json, hashlib
from collections import Counter
from pathlib import Path
root=Path(__file__).resolve().parent
raw=(root/'ordered_commutation_dag.json').read_bytes()
doc=json.loads(raw)

def freeze(x):
    return tuple(map(freeze,x)) if isinstance(x,list) else x

def I(x,y):return ('I',x,y)
def Q(i,x):return ('Q',i,x)
T=('zero',);F=('R',T,T)
def N(x):return I(x,F)
def D(i,x):return N(Q(i,N(x)))
a,b,x=(('parameter',v) for v in ('a','b','x'))

allowed={'K','S','DNE','rho2','rho6','oriented_rho4','hyp','mp','gen'}

def wellformed(t):
    assert isinstance(t,tuple)
    if t[0]=='zero': assert t==T;return
    if t[0]=='parameter':assert len(t)==2 and t[1] in {'a','b','x'};return
    assert len(t)==3 and t[0] in {'I','Q','R'}
    wellformed(t[1]);wellformed(t[2])

def schema(rule,args):
    if rule=='K':
        v,w=args;return I(v,I(w,v))
    if rule=='S':
        u,v,w=args;return I(I(u,I(v,w)),I(I(u,v),I(u,w)))
    if rule=='DNE':
        v,=args;return I(N(N(v)),v)
    if rule=='rho2':
        i,u,v=args;return I(Q(i,I(u,v)),I(Q(i,u),Q(i,v)))
    if rule=='rho6':
        i,v=args;return I(D(i,Q(i,v)),v)
    if rule=='oriented_rho4':
        aa,bb,v=args
        assert (aa,bb)==(a,b), 'Opposite orientation or changed labels used as an axiom'
        return I(Q(a,Q(b,v)),Q(b,Q(a,v)))
    raise AssertionError(rule)

forms=[];opens=[];parents=[]
for k,n in enumerate(doc['nodes']):
    assert set(n)=={'rule','formula','parents','args','open'}
    rule=n['rule'];assert rule in allowed
    f=freeze(n['formula']);wellformed(f)
    ps=n['parents'];args=freeze(n['args']);oo=n['open']
    assert all(isinstance(p,int) and 0<=p<k for p in ps)
    assert oo==sorted(set(oo))
    opened=set(oo)
    if rule=='hyp':
        assert ps==[] and args==(k,) and opened=={k}
    elif rule=='mp':
        assert len(ps)==2 and not args
        major,minor=ps
        assert forms[major]==I(forms[minor],f)
        assert opened==opens[major]|opens[minor]
    elif rule=='gen':
        assert len(ps)==1 and len(args)==1
        assert not opens[ps[0]], 'GEN applied under an open hypothesis'
        assert not opened and f==Q(args[0],forms[ps[0]])
    else:
        assert not ps and not opened
        assert f==schema(rule,args)
    forms.append(f);opens.append(opened);parents.append(ps)
expected={
 'reversed_commutation':I(Q(b,Q(a,x)),Q(a,Q(b,x))),
 'symmetry_unit':I(x,Q(a,D(a,x)))
}
assert set(doc['outputs'])==set(expected)
for name,n in doc['outputs'].items():
    assert isinstance(n,int) and 0<=n<len(forms)
    assert not opens[n] and forms[n]==expected[name]
reachable=set(doc['outputs'].values()); todo=list(reachable)
while todo:
    for p in parents[todo.pop()]:
        if p not in reachable:reachable.add(p);todo.append(p)
assert all(not opens[k] for k in reachable), 'The theorem dependency graph retains an assumption'
counts=Counter(n['rule'] for n in doc['nodes'])
reachable_counts=Counter(doc['nodes'][k]['rule'] for k in reachable)
orient=[k for k,n in enumerate(doc['nodes']) if n['rule']=='oriented_rho4']
assert len(orient)==1
assert freeze(doc['nodes'][orient[0]]['args'])==(a,b,N(Q(b,Q(a,x))))
record={
 'status':'INDEPENDENT_ORDERED_COMMUTATION_AUDIT_PASS',
 'reader_dependencies':'Python standard library only; no generator/kernel import or execution',
 'nodes':len(forms),'reachable_nodes_from_outputs':len(reachable),
 'rule_counts':dict(sorted(counts.items())),
 'reachable_rule_counts':dict(sorted(reachable_counts.items())),
 'reachable_graph_has_no_hypotheses':True,
 'oriented_axiom_nodes':orient,
 'only_oriented_axiom_labels':['a','b'],
 'oriented_axiom_matrix':'not(Box_b(Box_a(x)))',
 'gen_nodes':counts['gen'],'all_gen_premises_closed':True,
 'outputs_closed_and_exact':True,
 'no_constructor_injectivity_or_object_substitution_rule':True,
 'sha256':{name:hashlib.sha256((root/name).read_bytes()).hexdigest() for name in ['ordered_commutation.py','hilbert.py','ordered_commutation_dag.json']},
 'remaining_math_premises':['K/S/DNE supplied at all native natural code instances by inherited dominated-rho8 calibration','native constructors preserve displayed formula equalities, including I(0,0)=0','rho2/rho6 and theorem-only GEN are available for all indicated natural parameters'],
 'not_claimed':['proof-assistant kernel check','binary machine certification','state saving','whole AX ordered-parameter calibration']
}
(root/'independent_ordered_audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
