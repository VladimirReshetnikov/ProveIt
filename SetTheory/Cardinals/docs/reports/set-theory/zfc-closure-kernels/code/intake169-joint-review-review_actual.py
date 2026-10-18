"""Read root's existing result only; no supplied code or builder invocation."""
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/tmp/zfc-joint-equational-packet-root1')
checks = 0
pins = {}


def ck(v, msg):
    global checks
    checks += 1
    if not v:
        raise ValueError(msg)


def read(p, expected=None):
    p = Path(p)
    b = p.read_bytes()
    digest = hashlib.sha256(b).hexdigest()
    ck(expected is None or digest == expected, 'Hash mismatch: ' + str(p))
    pins[str(p)] = {'path': str(p), 'sha256': digest}
    return b


def pretty(t):
    return t if isinstance(t, str) else t[0] if len(t) == 1 else t[0] + '(' + ','.join(pretty(x) for x in t[1:]) + ')'


def main():
    # Own previously reviewed pure syntax counter, not a supplied encoder.
    helper = Path('/tmp/zfc-d584-opening-review/review_static.py')
    read(helper, '34e9af5816aa2f77163def0fcae15a6684e526e06aca84794833559fb9a96b1e')
    spec = importlib.util.spec_from_file_location('own_packet_syntax', helper)
    own = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(own)
    r = json.loads(read(ROOT / 'output/verification.json'))
    execution = json.loads(read(ROOT / 'execution.json'))
    ck(execution['exit_code'] == 0 and execution['timed_out'] is False, 'Root command did not complete successfully')
    ck(execution['command'] == ['python3', '-B', '/tmp/zfc-joint-equational-packet/build_joint.py', '--reference', str(ROOT / 'reference'), '--horn-helper', str(ROOT / 'horn_certificates.py'), '--output', str(ROOT / 'output')], 'Execution identity differs')
    ck(read(ROOT / 'stderr.log') == b'', 'Nonempty stderr')
    ck(r['status'] == 'PASS_FINITE_PACKET_CHECKS', 'Not complete PASS')
    ck(r['before'] == r['after'], 'Recorded inputs differ')
    for p, digest in r['before'].items():
        read(p, digest)
    ck(all(r[k] is False for k in ('supplied_search_executed', 'simulator_executed', 'compiler_executed')), 'Unexpected execution scope')
    prior_horn = json.loads(read(HERE / 'horn-review.json'))
    del prior_horn['reviewer_source']
    ck(r['horn_certificates'] == prior_horn, 'Embedded Horn certificates differ')
    ck(json.loads(read(ROOT / 'stdout.log')) == r['variants'], 'Raw stdout differs from record')
    mapping = {'signature_symbols': 'signature_symbols', 'variable_capacity': 'local_variable_capacity',
               'opcode_width': 'opcode_width', 'header_bits': 'signature_and_capacity_bits',
               'equation_bits': 'equation_payload_bits', 'endpoint_bits': 'ground_endpoint_bits',
               'complete_packet_bits': 'complete_packet_bits', 'equations': 'equations',
               'both_side_tree_nodes': 'both_side_tree_nodes'}
    for name, bits_expected, eq_expected, node_expected in [('dispatch_no_alias', 1768, 18, 421), ('dispatch_split_alias', 1750, 21, 415)]:
        v = r['variants'][name]
        for descriptor in v['files'].values():
            read(descriptor['path'], descriptor['sha256'])
        data = json.loads(read(ROOT / 'output' / (name + '.json')))
        metrics, bits = own.measure(data)
        ck(read(ROOT / 'output' / (name + '.bits')) == (bits + '\n').encode(), 'Independent serialized term reconstruction differs')
        text = '\n'.join(f'{i}: {pretty(a)} = {pretty(b)}' for i, (a, b) in enumerate(data['equations'])) + '\n'
        ck(read(ROOT / 'output' / (name + '.equations')) == text.encode(), 'Printed equations differ')
        for key, recordkey in mapping.items():
            ck(metrics[key] == v[recordkey], 'Metric mismatch: ' + key)
        ck((len(bits), metrics['equations'], metrics['both_side_tree_nodes']) == (bits_expected, eq_expected, node_expected), 'Unexpected actual result')
        ck(v['strict_truncations_rejected'] == len(bits) and v['malformed_or_trailing_rejected'] == 3 and v['contextual_orientations'] == 2 * eq_expected, 'Recorded finite-check census differs')
        ck(data['selector_congruence'] is False, 'Selector congruence unexpectedly added')
        ck(data['dropped_original_congruence_clause_indices'] == [15, 16, 18, 19, 20, 21], 'Dropped clause set differs')
        ck(sum(g['boolean_assignments'] for g in data['original_groups']) == v['checked_boolean_assignments'] == 94, 'Boolean group census differs')
    for p, pin in pins.items():
        ck(hashlib.sha256(Path(p).read_bytes()).hexdigest() == pin['sha256'], 'File changed at close')
    result = {'status': 'EXISTING_FINITE_PACKET_EVIDENCE_REVIEW_PASS', 'findings': [], 'checks': checks,
              'role': 'Independent existing-output reviewer; author of the Horn certificate helper and own syntax counter, not author/operator of the builder.',
              'verification': pins[str(ROOT / 'output/verification.json')], 'execution': pins[str(ROOT / 'execution.json')],
              'files': list(pins.values()), 'reviewer_source': {'path': str(Path(__file__)), 'sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
              'actual_results': {'dispatch_no_alias': {'bits': 1768, 'equations': 18, 'nodes': 421},
                                 'dispatch_split_alias': {'bits': 1750, 'equations': 21, 'nodes': 415, 'saving_against_delivered1768': 18}},
              'scope': 'Read/hash/independent syntax reconstruction of existing root-run output. No supplied code, builder, kernel replay, simulator, compiler or consistency search executed by this reviewer. Ordinary model calibration and binary implementation remain separate.'}
    p = HERE / 'joint-actual-review.json'
    p.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'checks': checks, 'receipt': str(p), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}))


if __name__ == '__main__':
    main()
