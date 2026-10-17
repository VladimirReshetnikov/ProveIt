#!/usr/bin/env python3
"""Finite controls of the exact circuit binary codec and fair search spec."""
from copy import deepcopy
from hashlib import sha256
from itertools import islice
import json
from pathlib import Path
import platform
import time

import term_codec as B
import term_circuits as V
import test_circuits as TC
import check_term254 as CT
import symbolic254 as S

BASE = Path(__file__).resolve().parent
TABLES = TC.TABLES


def main():
    started = time.monotonic()
    tests, corruptions = [], []
    specimens = [S.Raw(0), S.Raw(1, (0,), (S.Raw(0), S.Raw(0))),
                 S.Raw(2, (1,), (S.Raw(0),))]
    specimens += [S.Raw(tag, tuple(range(S.ARITY[tag]))) for tag in range(3, 11)]
    specimens += [S.Raw(11, (0, 1, 2))]
    controls = []
    for raw in specimens:
        term, goal = CT.convert_control(raw)
        controls.append((TC.from_term(term), goal))
    for original in (2, 3):
        cert, goal = deepcopy(controls[original])
        cert['nodes'].append(deepcopy(cert['nodes'][goal]))
        goal = len(cert['nodes']) - 1
        row = cert['proof_rows'][-1]
        row['formula'] = goal
        if row['tag'] >= 3:
            row['constructor_ids'][-1] = goal
        controls.append((cert, goal))
    d = json.loads((BASE/'deep-bundle-control.json').read_text())
    d['certificate']['format'] = 'term-c254-v1'
    controls.append((TC.from_term(d['certificate']), d['trusted_control_goal']))
    lengths = []
    for cert, goal in controls:
        word = B.encode(cert, TABLES)
        got = B.decode(word, TABLES)
        assert got == cert
        assert V.verify_certificate(got, TABLES, goal=goal)
        assert not B.accepts(word, TABLES)
        lengths.append(len(word))
    tests.append('15 positive controls roundtrip exactly, including all12 tags, duplicate outputs and2048-edge path; all reject at fixedF')

    n = lambda value: '1'*value+'0'
    tag = lambda value, width: format(value, '0'+str(width)+'b')
    malformed = {
        'empty': '', 'truncated_unary': '111111', 'nonbinary': '020',
        'node_count_before_allocation': n(8)+'0000',
        'row_count_before_allocation': n(0)+n(8)+'00000',
        'zero_alias': n(1)+tag(0,2)+n(0)+n(0)+n(0),
        'node_forward_reference': n(1)+tag(1,2)+n(1)+n(0)+n(0),
        'unknown_rule': n(0)+n(1)+tag(12,4)+n(0),
        'proof_forward_reference': n(0)+n(1)+tag(2,4)+n(0)+n(0)+n(0),
        'argument_reference': n(0)+n(1)+tag(2,4)+n(1)+n(0)+n(0),
        'formula_reference': n(0)+n(1)+tag(0,4)+n(1),
        'circuit_reference': n(0)+n(1)+tag(3,4)+n(0)+n(0)+n(0)+n(1)+n(0)*4,
        'truncated_circuit': n(0)+n(1)+tag(3,4)+n(0)+n(0)+n(0),
    }
    bundle_word = B.encode(controls[11][0], TABLES)
    malformed['truncated_path'] = bundle_word[:-1]
    malformed['unterminated_path_bit'] = bundle_word[:-1]+'1'
    malformed['leftover_bits'] = bundle_word+'0'
    malformed_reasons = {}
    for label, word in malformed.items():
        stats = {}
        assert B.decode(word, TABLES, stats=stats) is None, label
        malformed_reasons[label] = stats['reason']
        corruptions.append(label)
    truth_word = B.encode(controls[0][0], TABLES)
    assert len(truth_word) == 8
    assert all(B.decode(truth_word[:end], TABLES) is None for end in range(len(truth_word)))
    tests.append('16 malformed words and every proper prefix of8-bit truth control reject')

    cert = deepcopy(controls[0][0])
    cert['nodes'].append(['b', 1, 0, 0])
    cert['proof_rows'][0]['formula'] = 1
    word = B.encode(cert, TABLES)
    assert B.decode(word, TABLES) == cert
    assert not B.accepts(word, TABLES)
    tests.append('structural parser accepts well-shaped false truth row; exact verifier rejects it')

    cert = deepcopy(controls[11][0])
    cert['proof_rows'][-1]['gate_paths'][0] += [0]
    word = B.encode(cert, TABLES)
    assert B.decode(word, TABLES) == cert
    assert not B.accepts(word, TABLES)
    tests.append('well-shaped false gate path roundtrips but exact verifier rejects it')

    max_length = 17
    count = parsed = accepted = 0
    parsed_per_length = {}
    for length in range(max_length+1):
        this_parsed = 0
        for word in B.words_at_length(length):
            cert = B.decode(word, TABLES)
            count += 1
            if cert is not None:
                parsed += 1; this_parsed += 1
                assert B.encode(cert, TABLES) == word
                if V.verify_certificate(cert, TABLES):
                    accepted += 1
        parsed_per_length[str(length)] = this_parsed
    assert count == (1 << (max_length+1))-1
    assert accepted == 0  # a finite observed result, not a consistency theorem
    tests.append('all262143 words of length<=17 terminate; every successful parse re-encodes to the exact original word')

    expected = ['', '0', '1', '00', '01', '10', '11', '000']
    assert list(islice(B.words(), len(expected))) == expected
    sequence = list(islice(B.words(), 127))
    for i, word in enumerate(sequence):
        assert i == (1 << len(word))-1 + (int(word,2) if word else 0)
    finite = B.search_through(6, TABLES)
    assert finite == {'status':'no_fixedF_certificate_through_length',
                      'max_length':6,'tested_words':127}
    tests.append('length-lex order/rank on first127 words; bounded no-hit result is explicitly finite')

    old = B.accepts
    calls = []
    try:
        def controlled(word, tables):
            calls.append(word)
            return word == '0110'
        B.accepts = controlled
        assert B.semidecide(TABLES) == '0110'
        assert len(calls) == (1 << 4)-1 + 6 + 1
    finally:
        B.accepts = old
    tests.append('semidecider fair-enumeration harness reaches controlled word0110 at rank21; no logical acceptance inferred')

    old = V.constructor
    resource_word = B.encode(controls[2][0], TABLES)  # GEN invokes the core record check.
    try:
        for resource_type in (MemoryError, RecursionError):
            def exhausted(*_args, _kind=resource_type, **_kwargs):
                raise _kind('test resource exhaustion')
            V.constructor = exhausted
            try:
                B.accepts(resource_word, TABLES)
            except resource_type:
                pass
            else:
                raise AssertionError('resource exhaustion was converted to logical rejection')
    finally:
        V.constructor = old
    tests.append('MemoryError and RecursionError from inside the actual core propagate; neither becomes fuel-as-UNSAT/rejection')

    result = {
        'status':'PASS','python':platform.python_version(),
        'command':'uv run --no-project python -B test_codec.py',
        'elapsed_seconds':time.monotonic()-started,
        'scope':'Finite binary codec QA and fair-search executable specification; no compiled TM/state count, Lean or PA theorem',
        'all_rule_tags':list(range(12)), 'exact_roundtrip_positive_controls':len(controls),
        'same_controls_rejected_at_fixedF':len(controls),
        'control_word_lengths':lengths,
        'exhaustive_short_words':{'max_length':max_length,'words':count,
                                  'successful_parses':parsed,'fixedF_acceptances':accepted,
                                  'successful_parses_by_length':parsed_per_length},
        'malformed_reasons':malformed_reasons,
        'tests':tests,'bounded_search_control':finite,
        'source_sha256':{name:sha256((BASE/name).read_bytes()).hexdigest()
                         for name in ['term_codec.py','test_codec.py','term_circuits.py',
                                      'source50/data/spec254.json']},
    }
    (BASE/'codec-results.json').write_text(json.dumps(result,indent=2)+'\n')
    (BASE/'example-bundle.bits').write_text(bundle_word)
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
