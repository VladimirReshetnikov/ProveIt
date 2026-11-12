"""Build reviewable certificates; all constructors are untrusted."""
from pathlib import Path
import json
import checker as k
import control
import proof_tools as p


def certificate(proof):
    goal = k.prove(proof, p.INITIAL)
    data = {'goal': goal, 'proof': proof}
    k.check(data)
    control.check({'goal': goal, 'proof': p.to_control(proof)})
    return data


def examples():
    out = {}
    out['reflexivity'] = certificate(p.refl(0))
    for name, term in [('zero', 0), ('one', p.ONE), ('two', p.TWO)]:
        proof = p.transport(p.refl(term), p.refl(p.S(term)), p.S(p.V), p.V)
        out['transport_at_' + name] = certificate(proof)
    for name, source, target in [('zero_to_one', 0, p.ONE), ('one_to_zero', p.ONE, 0)]:
        proof = p.implication([source, target], [target, source],
                              lambda eq, ctx: p.symmetry(eq, ctx))
        out['symmetry_' + name] = certificate(proof)
    # A genuinely open source is retained inside a closed D-formula.  The
    # term template contains two nested iterator binders, with captured
    # outer parameters used beneath the inner one.
    template = p.I(p.V, p.ONE, p.U,
                   p.I(p.U, p.V, -100006, p.S(-100006)))
    goal = p.D([p.at(template, p.V, p.Y), p.at(template, p.V, p.Y)])
    z = -1
    step_value = p.S(z)
    opened = k.sub(goal[0], 0, 1)
    local = p.INITIAL + [([], k.sub(opened, z))]
    value = p.at(template, p.V, step_value)
    branch = p.transport(p.refl(step_value), p.refl(value), template, p.V, local)
    out['nested_iterator_binders'] = certificate(['i', goal[0], 0, branch])
    # Compound D-consequent under the assumption 0=1.  Its innermost
    # equation is obtained using the automatic two-row transport, then
    # introduced under both native binders.
    inner = p.D([p.C(p.Y, 0, p.ONE), 0])
    compound = p.D(inner)
    antecedent = [0, p.ONE]
    # An implication is encoded using formula selection; for this one the
    # outer case premise itself retains the equation antecedent.
    matrix = p.bind([p.C(p.Y, 0, p.ONE), p.C(p.Y, p.ONE, 0)], [p.X, p.Y])
    sym = p.symmetry(p.use(1, 0), p.INITIAL + [([], antecedent)])
    out['compound_arithmetic_implication'] = certificate(['i', matrix, p.ONE, sym])
    # Prove a compound D whose branch invokes a transport proof beneath
    # two independent eigenvariable scopes.
    compound_identity = p.D(p.D([p.C(p.Y, 0, p.ONE), p.C(p.Y, 0, p.ONE)]),
                            x=-100007, y=-100008)
    outer_body = k.sub(compound_identity[0], p.ONE, 1)
    outer_base = k.sub(outer_body, 0)
    outer_local = p.INITIAL + [([], outer_base)]
    inner_target = k.sub(outer_body, p.S(-1))
    inner_body = k.sub(inner_target[0], p.ONE, 1)
    inner_local = outer_local + [([], k.sub(inner_body, 0))]
    inner_step = k.sub(inner_body, p.S(-2))
    nested_eq = p.transport(p.refl(p.ONE), p.refl(inner_step[0]), p.V, p.V,
                            inner_local)
    out['compound_nested_D'] = certificate(['i', compound_identity[0], p.ONE,
        ['i', inner_target[0], p.ONE, nested_eq]])
    # Guard fallback: this D matrix has an unused witness.  Exporting
    # reflexivity must work whether or not an equation occurs at row one.
    ordinary = p.D([0, 0])
    ordinary_major = ['i', ordinary[0], 0, p.refl(0)]
    out['ordinary_elimination_fallback'] = certificate(['e', ordinary_major, p.refl(0)])
    # A naming equality with tau containing b.  Specialization is one pass,
    # including occurrences under iterator binders; the branch's closed
    # conclusion does not leak b.  Recursive replacement into tau would loop.
    self_term = p.I(p.X, 0, p.U, p.S(p.U))
    self_packet = p.D([p.C(p.Y, 0, p.X), p.C(p.Y, 0, self_term)])
    self_major = ['i', self_packet[0], 0, p.refl(0)]
    out['self_occurring_synthesized_term'] = certificate(['e', self_major, p.refl(0)])
    # Its branch must see the specialized clause, not the old clause.
    bound_packet = p.D([p.C(p.Y, 0, p.X), p.C(p.Y, 0, p.ONE)])
    bound_major = ['i', bound_packet[0], p.ONE, p.refl(p.ONE)]
    out['branch_uses_specialized_clause'] = certificate(
        ['e', bound_major, p.use(1, p.ONE, p.refl(0))])
    return out


def main():
    root = Path(__file__).resolve().parent
    directory = root / 'examples'
    controls = root / 'control_examples'
    directory.mkdir(exist_ok=True)
    controls.mkdir(exist_ok=True)
    data = examples()
    for name, item in data.items():
        (directory / (name + '.json')).write_text(json.dumps(item, indent=2) + '\n')
        control_item = {'goal': item['goal'], 'proof': p.to_control(item['proof'])}
        (controls / (name + '.json')).write_text(json.dumps(control_item, indent=2) + '\n')
    print(json.dumps({'certificates': len(data), 'names': sorted(data)}, indent=2))


if __name__ == '__main__':
    main()
