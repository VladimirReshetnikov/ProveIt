#!/usr/bin/env python3
"""ORIGINAL UNRUN record composer; root preflight required before its sole run.

Copy the exact frozen Accepted prefix as inert records, append three literal
centralizer relations, and expose fixed query ports. No parent program is run
or imported. No group word is reduced or evaluated, and no input n is supplied.
"""
from pathlib import Path
import hashlib
import json

PARENT = Path('/tmp/positive7_higman_literal_presentation_riemann.json')
PARENT_SHA = '35a24f7ff3878f132e9bb37fa76a0c21de31795c2f72ea9e497c5efb7d1c1a57'
LEMMA = Path('/tmp/positive7_higman_membership_word_problem_aristotle.md')
LEMMA_SHA = '964fb2bedf08cb5ff2c985076baeaf30235baf17e8169611cd809244d9f7d709'
OUTPUT = Path('/tmp/positive7_higman_centralizer_branch_riemann.json')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def serialized(record):
    return json.dumps(record, separators=(',', ':'), ensure_ascii=True).encode()


def inverse_letters(word):
    result = []
    for letter in word[::-1]:
        result.append(-letter)
    return result


def check_letters(word, upper):
    assert isinstance(word, list)
    assert all(type(letter) is int and 0 < abs(letter) <= upper for letter in word)


def main():
    assert not OUTPUT.exists(), 'First receipt exists; never replay this composer.'
    raw = PARENT.read_bytes()
    assert sha(raw) == PARENT_SHA
    lemma_raw = LEMMA.read_bytes()
    assert sha(lemma_raw) == LEMMA_SHA
    old = json.loads(raw)
    assert old['schema'] == 'positive7-preembedding-literal-presentation-v1'
    assert len(old['generators']) == 499 and len(old['relators']) == 17678
    assert len(old['trace']) == 124
    accepted_event = old['trace'][122]
    removed_event = old['trace'][123]
    assert accepted_event['id'] == 123 and accepted_event['label'] == 'Accepted'
    assert accepted_event['asserted_checkpoint'] == [498, 17676, 3]
    assert accepted_event['relator_interval'] == [17671, 17676]
    assert removed_event['label'] == 'X_U' and removed_event['id'] == 124
    assert removed_event['kind'] == 'two_relator_affine_line_transducer'
    assert removed_event['new_generator_ids'] == [499]
    assert removed_event['relator_interval'] == [17676, 17678]
    assert removed_event['before'] == accepted_event['after']
    assert removed_event['detail']['no_marker_cache_A_or_shift_transport'] is True
    assert old['generators'][498] == {
        'id': 499, 'name': 'X_U/t', 'event': 124, 'declared_after_relator': 17676}
    assert [r['event'] for r in old['relators'][17676:]] == [124, 124]

    # These are immutable record slices. No inherited word is transformed.
    prefix_generators = old['generators'][:498]
    prefix_relators = old['relators'][:17676]
    prefix_events = old['trace'][:123]
    assert [row['id'] for row in prefix_generators] == list(range(1, 499))
    assert [row['index'] for row in prefix_relators] == list(range(17676))
    for row in prefix_relators:
        assert 1 <= row['event'] <= 123
        for field in ('stable', 'source', 'target', 'word'):
            check_letters(row[field], 498)
    assert all('X_U' not in row['name'] for row in prefix_generators)
    accepted = old['cached_lists']['Accepted']
    assert accepted == accepted_event['created_lists']['Accepted']
    assert accepted == [
        [-498, -497, 467, 497, 498],
        [-498, -497, 468, 497, 498],
        [-498, -497, 469, 497, 498]]
    marker = accepted_event['after']['marker_ids']
    assert marker == [467, 468, 469]
    assert old['final_state']['marker_ids'] == marker
    for field in ('tracked_A', 'global_shift_word'):
        assert old['final_state'][field] == accepted_event['after'][field]

    # Fresh branch identity: local ID499 does not denote the discarded X_U/t.
    new_generator = {'id': 499, 'name': 'centralizer/t', 'event': 124,
                     'declared_after_relator': 17676}
    additions = []
    for slot, word in enumerate(accepted):
        additions.append({
            'index': 17676 + slot, 'event': 124, 'family': 'centralizer/fix/' + str(slot),
            'stable': [499], 'source': list(word), 'target': list(word),
            'word': [-499] + word + [499] + inverse_letters(word)})
    generators = prefix_generators + [new_generator]
    relators = prefix_relators + additions
    assert generators[:498] == prefix_generators
    assert relators[:17676] == prefix_relators
    assert len(generators) == 499 and len(relators) == 17679
    assert len({row['name'] for row in generators}) == 499
    for row in additions:
        assert row['source'] == row['target']
        check_letters(row['word'], 499)
        assert row['word'].count(499) == 1 and row['word'].count(-499) == 1

    # Construct only the fixed ports. W_n remains text; no n is instantiated.
    a, b, c = marker
    alpha = [-b] * 23 + [a] + [b] * 23
    beta = [-c, b, c]
    query_ports = {'alpha': alpha, 'beta': beta, 't': [499]}
    for word in query_ports.values():
        check_letters(word, 499)

    # A small catalog resolves every inherited event ID without carrying the
    # X_U cache, trace event, selected list, final census or transducer metadata.
    event_catalog = []
    for event in prefix_events:
        event_catalog.append({
            'id': event['id'], 'label': event['label'], 'kind': event['kind'],
            'new_generator_ids': event['new_generator_ids'],
            'relator_interval': event['relator_interval'],
            'parent_event_sha256': sha(serialized(event))})
    event_catalog.append({
        'id': 124, 'label': 'centralizer', 'kind': 'identity_HNN_on_Accepted',
        'new_generator_ids': [499], 'relator_interval': [17676, 17679]})
    assert [event['id'] for event in event_catalog] == list(range(1, 125))
    for event in event_catalog:
        first, last = event['relator_interval']
        assert all(row['event'] == event['id'] for row in relators[first:last])
    for row in generators:
        assert row['id'] in event_catalog[row['event'] - 1]['new_generator_ids']

    source_raw = Path(__file__).read_bytes()
    result = {
        'schema': 'positive7-Accepted-centralizer-literal-v1',
        'scope': 'Direct identity-HNN word-problem branch; no two-generator or arithmetic-interface expansion.',
        'source': {'path_at_first_run': str(Path(__file__)), 'sha256': sha(source_raw),
                   'bytes': len(source_raw), 'LF_lines': source_raw.count(b'\n')},
        'parent': {'path': str(PARENT), 'sha256': PARENT_SHA, 'bytes': len(raw),
                   'prefix_generator_interval': [0, 498], 'prefix_relator_interval': [0, 17676],
                   'prefix_generators_sha256': sha(serialized(prefix_generators)),
                   'prefix_relators_sha256': sha(serialized(prefix_relators)),
                   'prefix_trace_interval': [0, 123], 'prefix_trace_sha256': sha(serialized(prefix_events)),
                   'Accepted_event_sha256': sha(serialized(accepted_event)),
                   'omitted_tail_generator_interval': [498, 499],
                   'omitted_tail_relator_interval': [17676, 17678],
                   'record_retention': 'Every retained generator/relator object equals the exact parent slice.'},
        'mathematical_premise': {'path': str(LEMMA), 'sha256': LEMMA_SHA,
                                'bytes': len(lemma_raw), 'LF_lines': lemma_raw.count(b'\n')},
        'generators': generators, 'relators': relators, 'event_catalog': event_catalog,
        'marker_ids': marker, 'Accepted_words': accepted, 'query_ports': query_ports,
        'query_family': {
            'parameter': 'ordinary integer n, not instantiated by this composer',
            'h_n': 'inverse(beta^n) alpha beta^n',
            'W_n': 'inverse(h_n) inverse(t) h_n t',
            'claim': 'W_n=1 in the presented group iff n belongs to the fixed universal set U',
            'status': 'symbolic word notation only, justified by the separately pinned HNN/free-basis proof'},
        'word_conventions': {'letters': 'flat signed generator IDs; no reduction',
                             'fix_relation': 'inverse(t) ell_i t inverse(ell_i)',
                             'commutator': '[h,t]=inverse(h) inverse(t) h t'},
        'census': {'generators': 499, 'relators': 17679, 'inherited_generators': 498,
                   'inherited_relators': 17676, 'new_generators': 1, 'new_relators': 3,
                   'Accepted_words': 3, 'new_relation_lengths': [len(r['word']) for r in additions],
                   'fixed_query_port_lengths': {key: len(word) for key, word in query_ports.items()}},
        'boundaries': [
            'The original X_U output is unchanged; this is a separate branch from Accepted.',
            'Only the three Accepted words are centralized, not all ambient generators.',
            'No parameter query is instantiated or evaluated.',
            'No inherited X_U cache, final-state, selected-list or transducer metadata is active.',
            'The faithful two-generator/matrix/paid arithmetic interface remains open.'],
        'status': 'first original inert-prefix/literal-suffix composition; independent review separate'}
    encoded = serialized(result) + b'\n'
    with OUTPUT.open('xb') as stream:
        stream.write(encoded)
    print(json.dumps({'status': 'PASS', 'output': str(OUTPUT), 'sha256': sha(encoded),
                      'bytes': len(encoded), 'census': result['census']}))


if __name__ == '__main__':
    main()
