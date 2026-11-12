"""Reproduce symbolic certificate generation and focused CLI boundary checks."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "code"))
from producer import *

HERE = Path(__file__).resolve().parent
DEFAULT_KERNEL = HERE.parent / 'code' / 'checker.py'


def generalize(builder):
    y, x, z = fresh('general'), fresh('unused'), fresh('general_eigen')
    matrix = builder(V(y)).goal
    return di(D(x, y, matrix), S(Z), z, builder(S(V(z))), False)


def lift(p, depth):
    for _ in range(depth):
        x, y, z = fresh('unused'), fresh('unused'), fresh('lift_eigen')
        p = di(D(x, y, p.goal), S(Z), z, p, False)
    return p


def motive(v, depth):
    f = Eq(v, num(2))
    for _ in range(depth): f = D(fresh('unused'), fresh('unused'), f)
    return f


def compound_transport(depth):
    e = computation(W(S(num(2))))
    x = fresh('hole')
    return transport(e, x, motive(V(x), depth), lift(e, depth))


def compound_identity(depth):
    f = Eq(num(2), num(3))
    for _ in range(depth): f = D(fresh('unused'), fresh('unused'), f)
    x, y, z = fresh('unused'), fresh('unused'), fresh('identity_eigen')
    return di(D(x, y, f), S(Z), z, hyp(f), False)


def reuse_clause():
    x, y, z, a = fresh('unused'), fresh('bound'), fresh('eigen'), fresh('witness')
    body = Eq(V(y), V(y))
    major = di(D(x, y, body), S(Z), z, refl(S(V(z))), False)
    clause = Q(y, body)
    p = qe(hyp(clause), S(Z), refl(Z))
    return de(major, a, trans(p, p))


def nonvacuous_transport():
    e = computation(W(S(num(2))))
    s, t = e.goal[1:]
    hole, x, y, z = fresh('hole'), fresh('witness'), fresh('unused'), fresh('eigen')
    f = D(x, y, Eq(S(V(x)), S(V(hole))))
    minor_formula = subst(f, hole, s)
    minor = di(minor_formula, s, z, refl(S(s)), False)
    return transport(e, hole, f, minor)


def induction_example():
    h = lambda u, v: S(v)
    j = lambda n: J(n, Z, h)
    y = fresh('counter')
    body = Eq(j(V(y)), V(y))
    def step(z):
        p = j_successor(z, Z, h)
        q = congruence(hyp(Eq(j(z), z)), S)
        return trans(p, q)
    return prove_instance(y, body, j_zero(Z, h), step, num(2), True)


def zero_witness_example():
    x, y, z = fresh('witness'), fresh('unused'), fresh('eigen')
    return di(D(x, y, Eq(V(x), Z)), Z, z, refl(Z), False)


def conditional_false_base():
    # With base 0=1, transport the counter in W(S(z))=z from 0 to 1
    # after a constant-body recursion to derive arbitrary equations.
    x, y, z = fresh('unused'), fresh('counter'), fresh('eigen')
    body = Eq(V(y), S(Z))
    assumed = hyp(Eq(Z, S(Z)))
    hole = fresh('hole')
    # Under 0=1, use the R-counter selector:
    # R(0,a;0)=Sa, R(1,a;0)=0, hence Sa=0. Use a=z.
    ax2 = computation(R(Z, V(z), lambda u,v: Z))
    tmpl2 = Eq(R(V(hole), V(z), lambda u,v: Z), S(V(z)))
    moved2 = transport(assumed, hole, tmpl2, ax2)
    red2 = computation(R(S(Z), V(z), lambda u,v: Z))
    s_eq_zero = symmetry(trans(symmetry(red2), moved2)) # Sz=0
    step = trans(s_eq_zero, assumed) # Sz=1
    return di(D(x,y,body), S(Z), z, step, False)


def source_cases():
    cases = [
        ('R_base', computation(R(Z, num(2), lambda u,v: v))),
        ('R_counter_slot', computation(R(S(Z), Z, lambda u,v: u))),
        ('R_state_slot', computation(R(S(Z), Z, lambda u,v: v))),
        ('R_nested_update', generalize(lambda n: computation(R(S(n), n,
             lambda u,v: R(S(u), v, lambda a,b: S(a)))))),
        ('J_zero_symbolic', generalize(lambda a: j_zero(a, lambda u,v: S(v)))),
        ('J_successor_two_parameters', generalize(lambda a: generalize(
             lambda n: j_successor(n, a, lambda u,v: R(S(u), v, lambda c,s: S(s)))))),
        ('reused_internal_clause', reuse_clause()),
        ('nonvacuous_witness_transport', nonvacuous_transport()),
        ('literal_equation_induction', induction_example()),
        ('zero_witness_box', zero_witness_example()),
        ('conditional_false_base', conditional_false_base()),
    ]
    cases += [('compound_identity_depth_'+str(d), compound_identity(d)) for d in [1,2,3]]
    cases += [('compound_transport_depth_'+str(d), compound_transport(d)) for d in [1,2,3]]
    return cases


def run(kernel=DEFAULT_KERNEL):
    output = []
    for label, proof in source_cases():
        packet_, counts = produce(proof)
        output.append({'name':label, 'expected':True, 'packet':packet_, 'nodes':len(packet_)-1, 'counts':counts})
    raw_direct, counts = serialize(compound_transport(1), permit_compound_transport=True)
    output.append({'name':'direct_compound_transport_rejected', 'expected':False, 'packet':raw_direct})
    comp = [0,0,0,0]
    negatives = [
        ('false_equation', [comp, [0,[0]]]),
        ('free_negative_goal', [comp, [[0,-1,0],[-1]]]),
        ('free_positive_goal', [comp, [[0,5,0],[5]]]),
        ('wrong_base_result', [comp, [[0,0,0],0]]),
        ('two_child_counter_ignored_update', [comp, [[[0,0],0,0],0]]),
        ('three_child_counter_ignored_update', [comp, [[[0,0,0],0,0],0]]),
        ('four_child_goal', [comp,[0,0,0,0]]),
        ('scalar_template_no_indexing', [[[[0,0,0],[0]],[0,0,0],[0],0],[[0],[0]]]),
    ]
    output += [{'name':label,'expected':False,'packet':packet_} for label,packet_ in negatives]
    # Every field guard is exercised using a valid transport derivation.
    transport_packet, _ = produce(refl(Z))
    for label, index, replacement in [
        ('wrong_transport_source',1,[[0]]),
        ('wrong_transport_target',2,[[0]]),
        ('wrong_transport_template',3,[1,[[0]]]),
    ]:
        packet_ = copy.deepcopy(transport_packet)
        packet_[-2][index] = replacement
        output.append({'name':label,'expected':False,'packet':packet_})
    results = []
    for case in output:
        for optimized in [False,True]:
            command = [sys.executable] + (['-O'] if optimized else []) + [str(kernel)]
            p = subprocess.run(command,input=json.dumps(case['packet']),text=True,capture_output=True,timeout=30)
            actual = p.returncode == 0 and p.stdout == 'ACCEPT\n'
            results.append({'name':case['name'],'optimized':optimized,'expected':case['expected'],
                            'actual':actual,'exit_code':p.returncode,'stdout':p.stdout.strip()})
            if actual != case['expected']:
                print('FAILED',case['name'],optimized,p.stderr)
                raise AssertionError(case['name'])
    evidence = {'kernel':str(kernel), 'sha256':hashlib.sha256(Path(kernel).read_bytes()).hexdigest(),
                'case_count':len(output),'positive':sum(c['expected'] for c in output),
                'negative':sum(not c['expected'] for c in output),'cli_runs':len(results),
                'passed':True,'results':results}
    (HERE/'certificates.json').write_text(json.dumps(output,indent=2)+'\n')
    (HERE/'validation.json').write_text(json.dumps(evidence,indent=2)+'\n')
    example_dir = HERE/'examples'
    example_dir.mkdir(exist_ok=True)
    for case in output:
        (example_dir/(case['name']+'.json')).write_text(json.dumps(case['packet'],indent=2)+'\n')
    print(json.dumps({k:v for k,v in evidence.items() if k!='results'},indent=2))
    return evidence


if __name__ == '__main__':
    run(Path(sys.argv[1]).resolve() if len(sys.argv)>1 else DEFAULT_KERNEL)
