"""Untrusted named proof translation to deterministic-witness DI.

The complete checker imports neither this file nor inherited_producer.py.
The inherited producer is copied unchanged from the certified-zero draft.
New work here: admissible normalization of two DI modes into a witness rule.
"""
import copy
import json
from pathlib import Path

import inherited_producer as p


CHILDREN = ('major', 'minor', 'premise', 'continuation')


def cut_hypothesis(proof, formula, replacement):
    """Substitute a derivation for uses of a retained named assumption.

All generated fresh names avoid the entire source tree. The replacement's
free variables are among the source assumption's fixed parameters, so this
ordinary-assumption cut preserves every inner eigenvariable condition.
    """
    if proof['rule'] == 'Hyp' and proof['goal'] == formula:
        return replacement
    result = dict(proof)
    for key in CHILDREN:
        if key in result:
            result[key] = cut_hypothesis(result[key], formula, replacement)
    return result


class Normalizer:
    def __init__(self, source):
        self.reserved = repr(source)
        self.serial = 0
        self.events = []

    def fresh(self, purpose):
        while True:
            self.serial += 1
            name = '_witness_normal_' + str(self.serial) + '_' + purpose
            if name not in self.reserved:
                self.reserved += ' ' + name
                return name

    def proof(self, source):
        proof = dict(source)
        for key in CHILDREN:
            if key in proof:
                proof[key] = self.proof(proof[key])
        if proof['rule'] != 'DI':
            return proof
        _, x, y, body = proof['goal']
        witness, eigen = proof['witness'], proof['eigen']
        if body[0] != 'eq':
            # A compound progress tree is deliberately left forged; the
            # independently checked negative examples must still reject it.
            return proof
        if proof['mode'] == 'progress' and witness != 0:
            body_at_witness = p.substitute(body, x, witness)
            dummy = self.fresh('dummy')
            discarded = self.fresh('discarded')
            outer_eigen = self.fresh('case')
            closure_goal = p.D(dummy, y, body_at_witness)
            zero_progress = p.introduction(closure_goal, 0, eigen, 'progress',
                                           proof['premise'])
            closure = p.Q(y, body_at_witness)
            base = p.substitute(body_at_witness, y, 0)
            successor = p.specialize(p.hyp(closure), p.S(p.V(outer_eigen)),
                                     p.hyp(base), role='witness_rule_specialization')
            outer_case = p.introduction(proof['goal'], witness, outer_eigen,
                                        'case', successor)
            result = p.elimination(zero_progress, discarded, outer_case)
            self.events.append({'transformation': 'nonzero_progress',
                                'goal': proof['goal'], 'witness': witness})
        elif proof['mode'] == 'case' and witness == 0:
            hole = self.fresh('zero_hole')
            state = self.fresh('zero_state')
            sym_name = self.fresh('symmetry')
            certified_zero = p.I(p.TWO, p.ONE, state, 0)
            zero_equation = p.compute(certified_zero)
            base_motive = p.substitute(p.substitute(body, x, p.V(hole)), y, 0)
            old_base = p.substitute(base_motive, hole, 0)
            new_base = p.substitute(base_motive, hole, certified_zero)
            base_bridge = p.transport(zero_equation, hole, base_motive,
                                      p.hyp(new_base),
                                      role='witness_rule_base_transport')
            minor = cut_hypothesis(proof['premise'], old_base, base_bridge)
            step_motive = p.substitute(p.substitute(body, x, p.V(hole)), y,
                                      p.S(p.V(eigen)))
            lifted = p.transport(p.symmetry(zero_equation, sym_name), hole,
                                 step_motive, minor,
                                 role='witness_rule_successor_transport')
            result = p.introduction(proof['goal'], certified_zero, eigen,
                                    'case', lifted)
            self.events.append({'transformation': 'zero_case',
                                'goal': proof['goal'], 'witness': certified_zero})
        else:
            return proof
        if result['goal'] != proof['goal']:
            raise ValueError('DI translation changed its end formula')
        return result


def normalize(proof):
    normalizer = Normalizer(proof)
    result = normalizer.proof(proof)
    return result, normalizer.events


def marker_normalize(packet):
    result = copy.deepcopy(packet)
    for command in result[:-1]:
        if isinstance(command, list) and len(command) == 4 and not command[0]:
            command[0] = []
    return result


class Emitter(p.Emitter):
    def packet(self, proof):
        normalized, self.normalization_events = normalize(proof)
        return marker_normalize(super().packet(normalized))


def supplementary_proofs():
    """Exercise both transformations with genuinely used assumptions."""
    x, y, z = 'extra_zero_x', 'extra_zero_y', 'extra_zero_z'
    body = p.Eq(p.C(p.V(y), p.ONE, p.S(p.V(x))), 0)
    goal = p.D(x, y, body)
    # This case step deliberately requires its zero-instance hypothesis:
    # extraction yields 1=0, then transport identifies the computed step.
    # In this specialization the witness remains 0 in both local formulas.
    instantiated_base = p.hyp(p.substitute(p.substitute(body, x, 0), y, 0))
    base_computation = p.compute(p.C(0, p.ONE, p.ONE))
    extracted = p.transitivity(p.symmetry(base_computation, 'extra_base_sym'),
                              instantiated_base, 'extra_base_join')
    step_computation = p.compute(p.C(p.S(p.V(z)), p.ONE, p.ONE))
    step = p.transitivity(step_computation, extracted, 'extra_zero_step')
    zero_case = p.introduction(goal, 0, z, 'case', step)
    n, state = 'extra_progress_n', 'extra_progress_state'
    def successor(k):
        current = p.I(k, p.ONE, state, p.V(state))
        next_value = p.I(p.S(k), p.ONE, state, p.V(state))
        return p.transitivity(p.compute(next_value),
                              p.hyp(p.Eq(current, p.ONE)), 'extra_progress_join')
    witness_name, step_name = 'extra_progress_witness', 'extra_progress_step'
    dependent_body = p.Eq(p.I(p.V(n), p.V(witness_name), state, p.V(state)),
                           p.V(witness_name))
    nonzero_progress = p.introduction(p.D(witness_name, n, dependent_body),
                                     p.ONE, step_name, 'progress',
                                     successor(p.V(step_name)))
    return [('zero_case_uses_base', zero_case),
            ('nonzero_progress_uses_IH', nonzero_progress)]


def build_positive_cases():
    inherited = p.build_cases()
    selected = [(c['name'], c['proof_tree']) for c in inherited
                if c['accept'] and 'proof_tree' in c]
    selected.append(('literal_zero_seed_restored_by_three_node_normalization',
                     p.compute(p.I(0, 0, 'restored_zero_seed_state', 0))))
    selected.append(('certified_zero',
                     p.compute(p.I(p.TWO, p.ONE, 'certified_zero_state', 0))))
    selected.extend(supplementary_proofs())
    result = []
    for name, proof in selected:
        emitter = Emitter()
        packet = emitter.packet(proof)
        result.append({'name': name, 'accept': True, 'packet': packet,
                       'trace': emitter.trace,
                       'normalization_events': emitter.normalization_events,
                       'source_proof': proof})
    return result


if __name__ == '__main__':
    cases = build_positive_cases()
    Path(__file__).with_name('witness_cases.json').write_text(
        json.dumps(cases, indent=2) + '\n')
    print(json.dumps({'positive_cases': len(cases),
                      'normalization_events': sum(len(c['normalization_events'])
                                                  for c in cases)}))
