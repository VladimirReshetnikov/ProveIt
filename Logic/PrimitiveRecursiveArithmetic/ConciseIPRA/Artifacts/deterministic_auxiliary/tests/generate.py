"""Untrusted proof generation for the deterministic auxiliary calculus.

Frozen vendor modules are attributed in reference/PROVENANCE.json.
No standalone checker imports this file or any of its dependencies.
The only changed derived construction is numerical cases: an equation
uses progress with an unused induction hypothesis; a compound uses cases.
"""
import copy
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent / 'vendor'))
import native_producer as p
import global_producer as gp
import normalizer as n
import build_root_cases as guarded


def numerical_cases(index, body, base, step, target):
    mode = 'progress' if body[0] == 'eq' else 'case'
    closure = p.make_closure(index, body, step, mode=mode,
                             prefix=n.fresh('deterministic_cases'))
    return p.specialize(closure, target, base)


n.numerical_cases = numerical_cases


def inspect(proof):
    result = dict(nodes=0, zero_source_transport=0,
                  atomic_case_introductions=0, compound_progress=0,
                  unguarded_atomic_progress=0, rules={})
    seen = set()
    def walk(node):
        if id(node) in seen:
            return
        seen.add(id(node))
        result['nodes'] += 1
        rule = node['rule']
        result['rules'][rule] = result['rules'].get(rule, 0) + 1
        if rule == 'Tr' and node['major']['goal'][1] == 0:
            result['zero_source_transport'] += 1
        if rule == 'DI':
            _, _, y, matrix = node['goal']
            atomic = matrix[0] == 'eq'
            result['atomic_case_introductions'] += atomic and node['mode'] != 'progress'
            result['compound_progress'] += not atomic and node['mode'] != 'case'
            if atomic:
                is_guard = all(isinstance(t, tuple) and t[0] == 'i'
                               and t[1] == p.V(y) and t[2] == 0
                               for t in matrix[1:])
                result['unguarded_atomic_progress'] += not is_guard
        for field in ('major', 'minor', 'premise', 'continuation'):
            if field in node:
                walk(node[field])
    walk(proof)
    return result


def new_cases():
    for row in guarded.build_proofs():
        if row['expected']:
            yield row['name'], row['proof'], row['canonical_goal'], row.get('description', '')
    for target, label in [(p.ONE, 'one'),
                          (p.I(p.TWO, p.ONE, 'zero_box_update', 0), 'computable_zero')]:
        antecedent = p.Eq(0, target)
        consequent = p.Eq(target, 0)
        derived = n.zero_symmetry(p.hyp(antecedent))
        proof = guarded.implication_intro(antecedent, consequent, derived)
        yield 'zero_symmetry_' + label, proof, True, (
            'Canonical implication encoding 0=t implies t=0. The primitive '
            'proof uses an unguarded auxiliary induction invariant, '
            'but no primitive transport source is literal zero.')
    variable, eigen, unused = 'all_symmetry_value', 'all_symmetry_eigen', 'all_symmetry_unused'
    body = guarded.implication(p.Eq(0, p.V(variable)), p.Eq(p.V(variable), 0))
    target = p.S(p.V(eigen))
    antecedent, consequent = p.Eq(0, target), p.Eq(target, 0)
    step = guarded.implication_intro(
        antecedent, consequent, n.zero_symmetry(p.hyp(antecedent)),
        p.substitute(body, variable, target))
    universal = p.introduction(p.D(unused, variable, body), 0, eigen, 'case', step)
    yield 'zero_symmetry_all_numbers', universal, True, (
        'D with an unused witness and matrix (0=y implies y=0). Its zero '
        'matrix is independently provable, so its ordinary reading gives '
        'the universal zero-symmetry statement. The step keeps an arbitrary '
        'successor parameter fixed during auxiliary equation induction.')
    # Recover a forbidden transport at an equation, with an explicit zero
    # equality whose target is an iterator term denoting zero.
    box = p.I(0, 0, 'transport_box_state', 0)
    zero_to_box = p.symmetry(p.compute(box), 'zero_to_box_hole')
    h = 'forbidden_transport_hole'
    motive = p.Eq(p.S(p.V(h)), p.S(p.V(h)))
    original = p.transport(zero_to_box, h, motive,
                           p.reflexivity(p.ONE, 'one_reflexive'))
    yield 'derived_zero_source_equational_transport', original, True, (
        'A literal-zero primitive transport in the input proof is eliminated '
        'by the untrusted normalizer; the standalone kernel checks its expansion.')


def main():
    destination = ROOT / 'tests' / 'certificates'
    destination.mkdir(exist_ok=True)
    records = []
    for name, original, canonical, description in new_cases():
        reduced = n.eliminate_zero_sources(original)
        expanded = p.expand_proof(reduced)
        audit = inspect(expanded)
        bad = (audit['zero_source_transport'] or
               audit['atomic_case_introductions'] or audit['compound_progress'])
        if bad:
            raise ValueError((name, audit))
        record = dict(name=name, canonical_goal=canonical,
                      description=description, audit=audit, packets={})
        for style, emitter in [('local', p.Emitter), ('global', gp.Emitter)]:
            packet = emitter().packet(reduced)
            filename = name + '_' + style + '.json'
            text = json.dumps(packet, separators=(',', ':')) + '\n'
            (destination / filename).write_text(text)
            record['packets'][style] = dict(file=filename,
                                           instructions=len(packet)-1,
                                           bytes=len(text.encode()))
        records.append(record)
    (ROOT / 'evidence' / 'certificate_manifest.json').write_text(
        json.dumps(records, indent=2) + '\n')
    # This is intentionally not a valid public formula. The old calculus
    # proves its conditional reading, whereas the deterministic proof
    # rules assign it a progressive auxiliary reading and reject this proof.
    old_case = n.eliminate_zero_sources(guarded.old_atomic_case())
    for style, emitter in [('local', p.Emitter), ('global', gp.Emitter)]:
        (ROOT / 'tests' / 'negative' / ('old_atomic_case_' + style + '.json')).write_text(
            json.dumps(emitter().packet(old_case), separators=(',', ':')) + '\n')
    (ROOT / 'tests' / 'negative' / 'unproved_contradiction.json').write_text('[[0,[0]]]\n')
    print(json.dumps(dict(examples=len(records),
                          certificates=sum(len(r['packets']) for r in records),
                          primitive_audits_passed=True), indent=2))


if __name__ == '__main__':
    main()
