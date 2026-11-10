"""Regenerate named proofs and focused controls without importing a checker."""
import producer as p


def build_cases():
    cases = p.build_cases()
    cases.append({'name': 'literal_zero_seed_opcode_removed',
                  'packet': [[None, 0, 0, 0], [[0, 0, 0], 0]], 'accept': False,
                  'meaning': 'The old literal-zero-seed command is no longer computation.'})
    emitter = p.Emitter()
    proof = p.compute(p.I(0, 0, 'explicit_zero_state', 0))
    cases.append({'name': 'literal_zero_seed_restored_by_three_node_normalization',
                  'packet': emitter.packet(proof), 'accept': True,
                  'meaning': 'The same theorem is restored with the certified zero.',
                  'trace': emitter.trace, 'proof_tree': proof})
    emitter = p.Emitter()
    proof = p.compute(p.I(0, p.ONE, 'any_false_marker', 0))
    packet = emitter.packet(proof)
    if len(packet) != 2 or packet[0][0] is not None:
        raise ValueError('Unexpected computation certificate shape')
    packet[0][0] = False
    cases.append({'name': 'false_marker_computation', 'packet': packet, 'accept': True,
                  'meaning': 'Computation does not require a dedicated null opcode.'})
    fresh_packet = [0, 0, 3, 0]
    independent_goal = [[0, [0], 0], [0]]
    cases.append({'name': 'fresh_zero_instance_supply_then_independent_theorem',
                  'packet': [[None, 0, [0], 0], fresh_packet, independent_goal],
                  'accept': True,
                  'meaning': 'The generated H(k) has a known zero instance; an independent theorem closes the goal.'})
    cases.append({'name': 'fresh_zero_instance_cannot_prove_false',
                  'packet': [fresh_packet, [[0, 3, 0], [0]]], 'accept': False,
                  'meaning': 'The same fresh assumption cannot establish a closed false equation.'})
    return cases
