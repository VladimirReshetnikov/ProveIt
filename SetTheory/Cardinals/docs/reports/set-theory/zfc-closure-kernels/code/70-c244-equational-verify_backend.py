#!/usr/bin/env python3
"""Verify the exact conversion, a real rewrite proof, and finite model lifts."""
from __future__ import annotations
from copy import deepcopy
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
import build_equations as B
from equational_search import Kernel, freeze, substitute, variables, from_file

ROOT = Path(__file__).resolve().parent


def synthetic_demo():
    signature = {'d':0, 'top':0, 'p':2, 'N':2}
    p = ('p', B.D, B.D)
    equations = [B.SHEFFER, B.TOP_DEFINITION, (p,B.TOP), (p,B.N(B.TOP,B.TOP))]
    data = {'name':'artificial contradictory predicate instance', 'signature':signature,
            'equations':equations, 'start':B.N(B.TOP,B.TOP), 'target':B.TOP,
            'scope':'positive and negative copies of p(d,d); not FC13B or ZFC'}
    kernel = Kernel(signature, equations, data['start'], data['target'])
    proof = [{'rule':3, 'reverse':True, 'address':[], 'values':[]},
             {'rule':2, 'reverse':False, 'address':[], 'values':[]}]
    assert kernel.check(proof)
    code = kernel.encode_proof(proof)
    assert kernel.check(kernel.decode_proof(code))
    found = kernel.search(code+1)
    assert found is not None and found <= code
    mutations = []
    p1=deepcopy(proof);p1[0]['reverse']=False;mutations.append(p1)
    p1=deepcopy(proof);p1[0]['address']=[0];mutations.append(p1)
    p1=deepcopy(proof);p1[0]['address']=[2];mutations.append(p1)
    p1=deepcopy(proof);p1[0]['values']=[B.D];mutations.append(p1)
    p1=deepcopy(proof);p1[0]['rule']=True;mutations.append(p1)
    p1=deepcopy(proof);p1[0]['reverse']=1;mutations.append(p1)
    p1=deepcopy(proof);p1[0]['extra']='ignored?';mutations.append(p1)
    p1=deepcopy(proof);p1[1]['rule']=3;mutations.append(p1)
    assert all(not kernel.check(p) for p in mutations)
    for n in range(2000):
        assert kernel.encode_term(kernel.decode_term(n)) == n
        assert kernel.encode_proof(kernel.decode_proof(n)) == n
    (ROOT/'demo_theory.json').write_text(json.dumps(data,indent=2)+'\n')
    (ROOT/'demo_proof.json').write_text(json.dumps(proof,indent=2)+'\n')
    accepted, trace = kernel.check(proof, True)
    (ROOT/'demo_trace.json').write_text(json.dumps({'accepted':accepted, 'code':code,
         'first_accepted_code':found, 'trace':trace},indent=2)+'\n')
    return {'certificate_steps':len(proof), 'certificate_code':code,
            'first_accepted_code':found, 'exhaustively_searched_codes':found+1,
            'invalid_mutations_rejected':len(mutations),
            'term_codec_roundtrips':2000, 'proof_codec_roundtrips':2000}


def finite_models():
    checks = 0
    # The primary single-axiom theorem is cited, not proved by these tests.
    for atoms in [1,2,3]:
        top = (1<<atoms)-1
        def ev(t,env):
            return env[t] if isinstance(t,str) else top ^ (ev(t[1],env)&ev(t[2],env))
        for x,y,z in product(range(top+1), repeat=3):
            env={'x':x,'y':y,'z':z}
            assert ev(B.SHEFFER[0],env) == y
            checks += 1

    # A genuinely satisfying original structure M={0,1}, f(x)=1-x,
    # P(x,y) iff x!=y, for T={P(x,f(x)), not P(x,x)}.
    # Its powerset Boolean carrier is {0,1,2,3}; pi retracts the singleton
    # injection and maps every nonsingleton to the chosen default zero.
    def pi(a):
        return 1 if a == 2 else 0
    def singleton(a):
        return 1 << a
    def f(a):
        return singleton(1-pi(a))
    def p(a,b):
        return 3 if pi(a)!=pi(b) else 0
    for a in range(4):
        assert p(a,f(a)) == 3
        assert p(a,a) == 0
    # Every ultrafilter on this finite BA is evaluation at an atom. The
    # reverse model keeps the entire four-object carrier and original f;
    # it does not quotient that carrier by the ultrafilter.
    for bit in [1,2]:
        for a in range(4):
            assert bool(p(a,f(a)) & bit)
            assert not bool(p(a,a) & bit)
    assert f(0) != 0  # f is intentionally not a Boolean homomorphism.
    return {'single_law_powerset_tests':checks, 'forward_full_carrier_assignments':4,
            'reverse_ultrafilter_assignments':8,
            'object_function_not_boolean_homomorphism':True}


def fixed_frontend():
    data=json.loads((ROOT/'grouped.json').read_text())
    source=freeze(json.loads((ROOT/'reference/FC13B_complete.json').read_text()))
    seen=[]; cases=0
    for group in data['source_groups']:
        indices=group['source_indices'];seen += indices
        assert B.check_equation([source[i] for i in indices], freeze(group['equation']))
        cases += 1 << len({B.atom(l) for i in indices for l in source[i]})
    assert sorted(seen) == list(range(len(source))) and len(seen)==len(set(seen))
    signature,equations,start,target=B.decode_packet((ROOT/'grouped.bits').read_text().strip(),list(data['signature']))
    assert equations == [B.canonical_equation(freeze(e)) for e in data['equations']]
    kernel=Kernel(signature,equations,start,target)
    oriented=0
    # Exercise both orientations, all variables (including variables absent
    # from one side), and non-root contexts of every serialized equation.
    for i,(left,right) in enumerate(equations):
        vs=kernel.rule_variables[i]
        values=[B.D if n%2==0 else B.TOP for n in range(len(vs))]
        env=dict(zip(vs,values))
        a,b=substitute(left,env),substitute(right,env)
        for reverse in [False,True]:
            x,y=(b,a) if reverse else (a,b)
            step={'rule':i,'reverse':reverse,'address':[1], 'values':values}
            context=Kernel(signature,equations,B.N(B.D,x),B.N(B.D,y))
            assert context.check([step])
            assert context.check(context.decode_proof(context.encode_proof([step])))
            oriented += 1
    for bad in [(ROOT/'grouped.bits').read_text().strip()[:-1],
                (ROOT/'grouped.bits').read_text().strip()+'0']:
        try:B.decode_packet(bad,list(signature))
        except ValueError:pass
        else:raise AssertionError('malformed packet accepted')
    return {'source_clauses_covered_exactly_once':len(seen),
            'propositional_group_truth_assignments':cases,
            'equational_context_orientations_verified':oriented,
            'full_packet_roundtrip':True, 'truncated_and_extra_bit_packets_rejected':True}


def main():
    metrics=B.build()
    result={'scope':'finite frontend, exact equational certificate checker, fair numeric codec; no TM table',
            'frontend':fixed_frontend(), 'models':finite_models(), 'demo':synthetic_demo(),
            'metrics':metrics}
    (ROOT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
