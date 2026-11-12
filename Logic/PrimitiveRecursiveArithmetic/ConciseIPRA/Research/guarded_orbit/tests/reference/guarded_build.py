"""Untrusted named proof production for the root-deterministic experiment.

No checker imports this module.  The original producer is frozen from ProveIt
b17dd5487f34adea473a0204c5320fb3eeb8910e.  Canonical positive goals use
D over a literal equation only when both sides are I(y,0;...).
"""
import copy
import json
from pathlib import Path
import producer as P

serial = 0

def fresh(label):
    global serial
    serial += 1
    return f'new_{label}_{serial}'


def cut(proof, assumed, supplied):
    if proof['rule'] == 'Hyp' and proof['goal'] == assumed:
        return copy.deepcopy(supplied)
    out = dict(proof)
    for key in ('major', 'minor', 'premise', 'continuation'):
        if key in proof:
            out[key] = cut(proof[key], assumed, supplied)
    return out


def join(a, b):
    return P.transitivity(a, b, fresh('join'))


def sym(a):
    return P.symmetry(a, fresh('sym'))


def wrap_equation(proof, left, right):
    """left: L=s, proof: s=t, right: R=t -> L=R."""
    return join(left, join(proof, sym(right)))


def unwrap_equation(proof, left, right):
    """left: L=s, proof: L=R, right: R=t -> s=t."""
    return join(sym(left), join(proof, right))


def guard(index, equation):
    return P.Eq(P.C(index, 0, equation[1]), P.C(index, 0, equation[2]))


def at_guard(index, proof):
    goal = guard(index, proof['goal'])
    return wrap_equation(proof, P.compute(goal[1]), P.compute(goal[2]))


def remove_guard(index, proof):
    """Only use a syntactically successor index here."""
    assert index[0] == 's'
    return unwrap_equation(proof, P.compute(proof['goal'][1]),
                           P.compute(proof['goal'][2]))


def guard_zero(equation):
    goal = guard(0, equation)
    return join(P.compute(goal[1]), sym(P.compute(goal[2])))


def lift_formula(equation):
    x, y = fresh('lift_x'), fresh('lift_y')
    return P.D(x, y, guard(P.V(y), equation))


def lift_intro(proof, target=None):
    target = target or lift_formula(proof['goal'])
    x, y, body = target[1:]
    z = fresh('lift_z')
    following = P.substitute(P.substitute(body, x, 0), y, P.S(P.V(z)))
    premise = wrap_equation(proof, P.compute(following[1]), P.compute(following[2]))
    return P.introduction(target, 0, z, 'progress', premise)


def lift_elim(proof):
    _, x, y, matrix = proof['goal']
    a = fresh('lift_a')
    opened = P.substitute(matrix, x, P.V(a))
    at0 = P.substitute(opened, y, 0)
    base = join(P.compute(at0[1]), sym(P.compute(at0[2])))
    at1 = P.specialize(P.hyp(P.Q(y, opened)), P.ONE, base)
    answer = unwrap_equation(at1, P.compute(at1['goal'][1]), P.compute(at1['goal'][2]))
    return P.elimination(proof, a, answer)


def selection(index, left, right):
    return P.Eq(P.C(index, left[1], right[1]),
                P.C(index, left[2], right[2]))


def selection_wrap(index, left, right, proof):
    selected = selection(index, left, right)
    return wrap_equation(proof, P.compute(selected[1]), P.compute(selected[2]))


def selection_unwrap(proof):
    return unwrap_equation(proof, P.compute(proof['goal'][1]), P.compute(proof['goal'][2]))


def implication(left, right):
    a, y = fresh('imp_a'), fresh('imp_y')
    return P.D(a, y, lift_formula(selection(P.V(y), left, right)))


def implication_intro(left, right, proof, target=None):
    """Given a derivation of right under left, construct their implication."""
    assert proof['goal'] == right
    target = target or implication(left, right)
    _, x, y, body = target
    z = fresh('imp_z')
    base = P.substitute(P.substitute(body, x, 0), y, 0)
    obtained_left = selection_unwrap(lift_elim(P.hyp(base)))
    assert obtained_left['goal'] == left
    obtained_right = cut(proof, left, obtained_left)
    following = P.substitute(P.substitute(body, x, 0), y, P.S(P.V(z)))
    selected = selection_wrap(P.S(P.V(z)), left, right, obtained_right)
    lifted = lift_intro(selected, following)
    return P.introduction(target, 0, z, 'case', lifted)


def implication_elim(major, left, right, minor):
    assert minor['goal'] == left
    _, x, y, body = major['goal']
    a = fresh('imp_elim')
    opened = P.substitute(body, x, P.V(a))
    base = P.substitute(opened, y, 0)
    selected = selection_wrap(0, left, right, minor)
    proof_base = lift_intro(selected, base)
    at1 = P.specialize(P.hyp(P.Q(y, opened)), P.ONE, proof_base)
    answer = selection_unwrap(lift_elim(at1))
    assert answer['goal'] == right
    return P.elimination(major, a, answer)


def compound_cases(index, body, zero, eigen, successor, target):
    assert body[0] != 'eq'
    assert zero['goal'] == P.substitute(body, index, 0)
    assert successor['goal'] == P.substitute(body, index, P.S(P.V(eigen)))
    x, a = fresh('cases_x'), fresh('cases_a')
    paired = P.D(x, index, body)
    pack = P.introduction(paired, 0, eigen, 'case', successor)
    continuation = P.specialize(P.hyp(P.Q(index, body)), target, zero)
    return P.elimination(pack, a, continuation)


def guarded_induction(index, equation, base, step_builder):
    """Produce D_unused,index G_index E from ordinary equation-induction data.

    The proof uses a guarded induction hypothesis nontrivially.  Numerical
    cases for the implication J(y)->E(Sy) are implemented with compound DI;
    no unrestricted atomic case introduction is generated.
    """
    x, z, w = fresh('ind_x'), fresh('ind_z'), fresh('ind_w')
    J = guard(P.V(index), equation)
    after = P.substitute(equation, index, P.S(P.V(index)))
    phi = implication(J, after)
    J0 = P.substitute(J, index, 0)
    E0 = P.substitute(equation, index, 0)
    step0 = cut(step_builder(0), E0, base)
    phi0 = implication_intro(J0, step0['goal'], step0,
                             P.substitute(phi, index, 0))
    sw = P.S(P.V(w))
    Jsw = P.substitute(J, index, sw)
    Esw = P.substitute(equation, index, sw)
    steppos = cut(step_builder(sw), Esw, remove_guard(sw, P.hyp(Jsw)))
    phisw = implication_intro(Jsw, steppos['goal'], steppos,
                              P.substitute(phi, index, sw))
    phiz = compound_cases(index, phi, phi0, w, phisw, P.V(z))
    Jz = P.substitute(J, index, P.V(z))
    Esz = P.substitute(equation, index, P.S(P.V(z)))
    applied = implication_elim(phiz, Jz, Esz, P.hyp(Jz))
    following = at_guard(P.S(P.V(z)), applied)
    return P.introduction(P.D(x, index, J), 0, z, 'progress', following)


def old_atomic_case():
    """Old D_y(y=1) is vacuously true, but the new raw H reading is false."""
    x,y,z = fresh('old_x'),fresh('old_y'),fresh('old_z')
    a,b = P.S(P.V(z)),P.ONE
    premise = P.hyp(P.Eq(0,P.ONE))
    middle = P.congruence(premise, lambda v: P.C(v,a,b), fresh('explode'))
    answer = join(sym(P.compute(P.C(0,a,b))),
                  join(middle,P.compute(P.C(P.ONE,a,b))))
    return P.introduction(P.D(x,y,P.Eq(P.V(y),P.ONE)),0,z,'case',answer)


class LocalEmitter(P.Emitter):
    def emit(self, proof, context):
        saved = self.floor
        self.floor = -len(context)
        try:
            return super().emit(proof, context)
        finally:
            self.floor = saved


def make_packet(proof, lexical=True, neutral=True):
    emitter = (LocalEmitter if lexical else P.Emitter)()
    packet = emitter.packet(proof)
    if neutral:
        for command in packet[:-1]:
            major, source, target, template = command
            if not major:
                command[0] = []
                if not target:
                    command[2] = major
    return packet


def build_proofs():
    results=[]
    def add(name, proof, expected=True, canonical=True, description=''):
        results.append({'name':name,'proof':proof,'expected':expected,
                        'canonical_goal':canonical,'description':description})
    add('computation_zero', P.compute(P.I(0,P.TWO,'zero_state',P.ONE)))
    add('computation_successor', P.compute(P.I(P.TWO,P.ONE,'step_state',P.S(P.V('step_state')))))
    add('transport_reflexivity', P.reflexivity(P.TWO,'tworefl'))
    simple=P.compute(P.I(0,P.ONE,'lift_computation',P.TWO))
    lifted=lift_intro(simple)
    add('guarded_literal_equation_introduction', lifted)
    add('guarded_lift_elimination',lift_elim(lifted))
    left=P.Eq(P.TWO,P.TWO)
    implication_proof=implication_intro(left,left,P.hyp(left))
    add('compound_case_introduction',implication_proof)
    add('compound_implication_elimination',implication_elim(implication_proof,left,left,P.reflexivity(P.TWO,'imp_refl')))
    index=fresh('iter_index')
    state=fresh('iter_state')
    equation=P.Eq(P.I(P.V(index),0,state,P.V(state)),0)
    base=P.compute(P.I(0,0,state,P.V(state)))
    def step(n):
        current=P.I(n,0,state,P.V(state))
        following=P.I(P.S(n),0,state,P.V(state))
        return join(P.compute(following), P.hyp(P.Eq(current,0)))
    add('guarded_induction_with_used_hypothesis',guarded_induction(index,equation,base,step),
        description='Guarded DI derives a lifted identity-iterator invariant. Its step uses the guarded IH via compound numerical cases and implication macros.')
    add('unguarded_progressive_alias',P.identity_closure('raw_progress'),canonical=False,
        description='The final Q theorem is an administrative closure, outside the canonical object grammar; its proof contains an unguarded atomic D used with the H interpretation, and the step uses the literal equation IH.')
    add('old_atomic_case_D_y_eq_one',old_atomic_case(),expected=False,canonical=False,
        description='Accepted by the old checker; rejected by the deterministic candidate. The old ordinary Q reading is true and the new raw H reading is false at y=1.')
    return results


def main():
    target=Path(__file__).resolve().parent/'root_cases'
    target.mkdir(exist_ok=True)
    meta=[]
    for case in build_proofs():
        row={k:v for k,v in case.items() if k!='proof'}
        row['packets']={}
        for lexical,neutral,label in [(True,True,'local_neutral'),(False,False,'global_plain'),(False,True,'global_neutral')]:
            packet=make_packet(case['proof'],lexical,neutral)
            filename=case['name']+'_'+label+'.json'
            (target/filename).write_text(json.dumps(packet,separators=(',',':'))+'\n')
            row['packets'][label]={'filename':filename,'instructions':len(packet)-1}
        meta.append(row)
    (target/'cases.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps([{'name':r['name'],'instructions':r['packets']['local_neutral']['instructions'],'expected':r['expected']} for r in meta],indent=2))

if __name__=='__main__':main()
