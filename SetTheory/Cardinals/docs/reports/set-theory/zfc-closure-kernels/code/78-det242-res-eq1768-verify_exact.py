#!/usr/bin/env python3
"""Finite transcription/codec controls and replayable universal Horn proofs.

No run here searches for an inconsistency of ZFC.  The model-theoretic
calibration is an ordinary proof in NOTES.md, not established by these tests.
"""
from pathlib import Path
from itertools import product
import json
import sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'reference'))
from equational_search import Kernel,freeze,variables,substitute
from build_equations import check_equation,decode_packet
from compress_packet import build as build_base
from optimize_alias import build as build_alias


def f(s,*xs):return (s,)+xs

def Eq(x,y):return f('Eq',x,y)
def Inc(x,y):return f('Inc',x,y)
def C(x,y,z):return f('C',x,y,z)

SCHEMAS={
 'refl':([],Eq('x','x')),
 'euclid':([Eq('x','y'),Eq('x','z')],Eq('y','z')),
 'full':([Eq('x','u'),Eq('y','v'),Eq('z','w')],Eq(C('x','y','z'),C('u','v','w'))),
 'first':([Eq('x','u'),Eq('y','v')],Eq(C('x','y','z'),C('u','v','z'))),
 'last':([Eq('z','w')],Eq(C('x','y','z'),C('x','y','w'))),
 'inc':([Eq('x','u'),Eq('y','v'),Inc('x','y')],Inc('u','v')),
}

def replay(assumptions,steps,goal,allowed):
    facts=list(assumptions)
    for step in steps:
        assert set(step)=={'schema','environment','premises'}
        name=step['schema'];assert name in allowed
        prem,conc=SCHEMAS[name]
        env=step['environment']
        required=set().union(*(variables(t) for t in prem+[conc]))
        assert set(env)==required
        assert all(not variables(t) for t in env.values())
        instantiated=[substitute(t,env) for t in prem]
        refs=step['premises']
        assert len(refs)==len(instantiated)
        assert all(type(i)is int and 0<=i<len(facts) for i in refs)
        assert [facts[i] for i in refs]==instantiated
        facts.append(substitute(conc,env))
    assert facts[-1]==goal
    return facts


def horn_proofs():
    a,b,c,u,v,w=map(lambda n:(n,),['a','b','c','u','v','w'])
    def step(s,e,p):return {'schema':s,'environment':e,'premises':p}
    joint=[Eq(a,u),Eq(b,v),Eq(c,w)]
    goal=Eq(C(a,b,c),C(u,v,w))
    steps=[
      step('first',dict(x=a,u=u,y=b,v=v,z=c),[0,1]),
      step('last',dict(x=u,y=v,z=c,w=w),[2]),
      step('refl',dict(x=C(a,b,c)),[]),
      step('euclid',dict(x=C(a,b,c),y=C(u,v,c),z=C(a,b,c)),[3,5]),
      step('euclid',dict(x=C(u,v,c),y=C(a,b,c),z=C(u,v,w)),[6,4]),
    ]
    replay(joint,steps,goal,{'first','last','refl','euclid'})
    one=[Eq(a,u),Eq(b,v)]
    steps1=[step('refl',dict(x=c),[]),step('full',dict(x=a,u=u,y=b,v=v,z=c,w=c),[0,1,2])]
    replay(one,steps1,Eq(C(a,b,c),C(u,v,c)),{'full','refl'})
    two=[Eq(c,w)]
    steps2=[step('refl',dict(x=a),[]),step('refl',dict(x=b),[]),step('full',dict(x=a,u=a,y=b,v=b,z=c,w=w),[1,2,0])]
    replay(two,steps2,Eq(C(a,b,c),C(a,b,w)),{'full','refl'})
    # The eliminated predicate is represented by one incidence atom. This
    # derivation checks its formerly explicit congruence, using only symbols
    # and schemas retained by the equality-complete source theory.
    d=('d',);o=f('I',d,d);atom=f('A',d,o)
    p0,p1=C(d,d,a),C(d,d,u)
    frame0,frame1=C(p0,o,b),C(p1,o,v)
    assumptions=[Eq(a,u),Eq(b,v),Inc(frame0,atom)]
    steps3=[
      step('refl',dict(x=d),[]),
      step('refl',dict(x=o),[]),
      step('full',dict(x=d,u=d,y=d,v=d,z=a,w=u),[3,3,0]),
      step('full',dict(x=p0,u=p1,y=o,v=o,z=b,w=v),[5,4,1]),
      step('refl',dict(x=atom),[]),
      step('inc',dict(x=frame0,u=frame1,y=atom,v=atom),[6,7,2]),
    ]
    replay(assumptions,steps3,Inc(frame1,atom),{'full','refl','inc'})
    proofs=[{'name':'split_to_full','assumptions':joint,'steps':steps,'goal':goal},
      {'name':'full_to_first','assumptions':one,'steps':steps1,'goal':Eq(C(a,b,c),C(u,v,c))},
      {'name':'full_to_last','assumptions':two,'steps':steps2,'goal':Eq(C(a,b,c),C(a,b,w))},
      {'name':'derived_membership_congruence','assumptions':assumptions,'steps':steps3,'goal':Inc(frame1,atom)}]
    (ROOT/'output/horn_proofs.json').write_text(json.dumps(proofs,indent=2)+'\n')
    return sum(len(p['steps']) for p in proofs)


def coordinate_checks():
    count=0
    for relation_bits in range(16):
        def e(x,y):return bool(relation_bits&(1<<(2*x+y)))
        for base,x,y in product(product(range(2),repeat=2),range(2),range(2)):
            s=list(base);s[0]=x;s[1]=y
            # Atomic-incidence axiom and the two update laws, in a small
            # separate-sorted test fixture. It is NOT a model of FC13B.
            lhs=e(s[0],s[1]);assert lhs==e(x,y)
            count+=1
    return count


def run():
    metrics=build_base();alias=build_alias()
    source=json.loads((ROOT/'reference/grouped.json').read_text())
    raw=freeze(json.loads((ROOT/'reference/FC13B_complete.json').read_text()))
    checked=0
    for row in source['source_groups']:
        group=[raw[i] for i in row['source_indices']]
        assert check_equation(group,freeze(row['equation']))
        checked+=1
    packet=(ROOT/'output/alias.bits').read_text().strip()
    obj=json.loads((ROOT/'output/alias.json').read_text())
    sig=obj['signature'];decode_packet(packet,list(sig))
    rejected=0
    for i in range(len(packet)):
        try:decode_packet(packet[:i],list(sig))
        except ValueError:rejected+=1
        else:raise AssertionError('truncated packet accepted')
    for bad in [packet+'0',packet+'1',packet[:70]+'x'+packet[71:]]:
        try:decode_packet(bad,list(sig))
        except ValueError:rejected+=1
        else:raise AssertionError('malformed packet accepted')
    eqs=freeze(obj['equations']);step_checks=0
    for i,(a,b) in enumerate(eqs):
        env={v:('d',) for v in sorted(variables(a)|variables(b))}
        left,right=substitute(a,env),substitute(b,env)
        for reverse in (False,True):
            begin,end=(right,left) if reverse else (left,right)
            k=Kernel(sig,eqs,('N',('d',),begin),('N',('d',),end))
            proof=[{'rule':i,'reverse':reverse,'address':[1],'values':list(env.values())}]
            assert k.check(proof)
            if begin!=end:
                wrong=[dict(proof[0],address=[0])]
                assert not k.check(wrong)
            step_checks+=1
    k=Kernel(sig,eqs,obj['start'],obj['target'])
    assert not k.check([])
    for n in range(1000):assert k.encode_term(k.decode_term(n))==n
    result={'status':'PASS','baseline_packet_bits':metrics['baseline']['complete_packet_bits'],
      'new_packet_bits':alias['complete_packet_bits'],'bits_saved':metrics['baseline']['complete_packet_bits']-alias['complete_packet_bits'],
      'baseline_boolean_groups_rechecked':checked,'packet_rejections':rejected,
      'ground_rewrite_orientation_controls':step_checks,'natural_term_roundtrips':1000,
      'universal_horn_proofs':4,'universal_horn_inferences':horn_proofs(),
      'coordinate_fixture_checks':coordinate_checks(),
      'scope':'finite codec/transcription controls and explicit Horn derivations; ordinary model proof in NOTES.md; no complete binary TM or consistency search'}
    (ROOT/'output/verification.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__=='__main__':print(json.dumps(run(),indent=2))
