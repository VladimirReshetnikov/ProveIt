#!/usr/bin/env python3
"""Independent static audit. Standard-library rational algebra, no simulation.

Read frozen proofs as inert UTF-8 and other manifested files only as hash bytes.
Never import or run any packet code, consume saved event schedules, numerically
evolve signals, choose a next event, or invoke a proof assistant. All generated
rows are finite symbolic certificates for the words printed in the proofs.
Output must be outside both source trees. O_NOATIME is used when available.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import itertools
import json
import os
from pathlib import Path
import re

CLOCK_SHA = '00cac79979a17bb5f803b9e0ff97bde2ec1039b1544a4991406f32cb9a08885a'
MANIFEST_SHA = '1bca064140e6aa5827e8d727ffe491987e8cc4cbcf7e731aae1975a99fe486f1'
CORE_SHA = '85f5de45c0a30f8bdf45b82a613ef9e5a8c766b5d8215d17a3ebbbd0f60b370f'


def read_bytes(path):
    flags = os.O_RDONLY | getattr(os, 'O_NOATIME', 0)
    try:
        fd = os.open(path, flags)
    except PermissionError:
        fd = os.open(path, os.O_RDONLY)
    with os.fdopen(fd, 'rb') as stream:
        return stream.read()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, label):
    if not condition:
        raise ValueError(label)


def row(*values):
    return tuple(Q(v) for v in values)


def plus(*rows):
    return tuple(sum(column, Q(0)) for column in zip(*rows))


def mul(factor, vector):
    return tuple(Q(factor) * v for v in vector)


def minus(left, right):
    return plus(left, mul(-1, right))


def positive_on_gaps(vector):
    return min(vector) >= 0 and max(vector) > 0


def normalized(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {str(k): normalized(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [normalized(v) for v in value]
    return value


def table(proof, heading):
    lines = proof.splitlines()
    start = next(i for i, line in enumerate(lines) if line.startswith(heading))
    data = []
    for line in lines[start + 2:]:
        if not line.startswith('|'):
            break
        data.append([cell.strip() for cell in line.strip('|').split('|')])
    return data


def validate_manifest(root, manifest, fixed_hash=None):
    raw = read_bytes(root / 'MANIFEST.json')
    if fixed_hash:
        require(digest(raw) == fixed_hash, 'frozen manifest digest')
    obj = json.loads(raw)
    entries = obj['files']
    if isinstance(entries, dict):
        entries = [dict(path=p, sha256=h) for p, h in entries.items()]
    results = {}
    for entry in entries:
        relative = Path(entry['path'])
        require(not relative.is_absolute() and '..' not in relative.parts, 'safe manifest path')
        blob = read_bytes(root / relative)
        require(digest(blob) == entry['sha256'], 'manifest member digest: ' + str(relative))
        if 'bytes' in entry:
            require(len(blob) == entry['bytes'], 'manifest member size: ' + str(relative))
        results[str(relative)] = dict(sha256=digest(blob), bytes=len(blob))
    manifest.update(results)
    return obj


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--clock-root', required=True, type=Path)
    parser.add_argument('--core-root', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    clock_root, core_root, output = (p.resolve() for p in
                                     (args.clock_root, args.core_root, args.output))
    require(all(not output.is_relative_to(p) for p in (clock_root, core_root)),
            'output must be external to source trees')
    require(output != Path(__file__).resolve(), 'output must not overwrite checker')
    source_hashes = {'clock': {}, 'core': {}}
    manifest = validate_manifest(clock_root, source_hashes['clock'], MANIFEST_SHA)
    validate_manifest(core_root, source_hashes['core'])
    proof_raw = read_bytes(clock_root / 'PROOF.md')
    core_raw = read_bytes(core_root / 'PROOF.md')
    require(digest(proof_raw) == CLOCK_SHA, 'clock proof identity')
    require(digest(core_raw) == CORE_SHA, 'core proof identity')
    require(manifest['dependency']['sha256'] == CORE_SHA, 'declared dependency identity')
    proof, core = proof_raw.decode(), core_raw.decode()

    # Exact source anchors bind the human derivation to the preserved prose.
    anchors = {
        'core': ['Duration is 2(1+k)t.', '2[t+t/(1-e)]+2D.',
                 't -> t/2 -> t/2+D/40.', 't -> 2t -> 2t-D/20.',
                 'x, 2x/3, 4x/9, 16x/9,', '(y-4x)/2, 2(8x-y)/9, F.',
                 'x, 2x/3, 4x/9, 16x/9, 2x, 8x.', 'F=(10y-8x)/9.',
                 'there are exactly m inverse events.',
                 'three events and time D.', '12+14=26', '32 on positive'],
        'clock': ['{p_out,T} -> {p_in,T}', '{p_in,S}  -> {q_next,S}',
                  '{p_out,B} -> {p_out,B}', '{p_in,B}  -> {p_in,B}',
                  '{p_tr,B} -> {p_tr,B}', '{p_tr,T} -> {q_next,T}',
                  'The initial full-span loop is important:',
                  'at the same speed +1 formerly used for the next instruction',
                  't_n=30nD.', 'those are post-halt events',
                  'No firstness, priority, exhaustive-search, or optimality claim is made.']}
    for source, snippets in anchors.items():
        for snippet in snippets:
            require(snippet in {'core': core, 'clock': proof}[source], 'missing source anchor: ' + snippet)

    # Coordinates below are (D,t,s) until inverse output substitutions are made.
    D, T, S, ZERO = row(1, 0, 0), row(0, 1, 0), row(0, 0, 1), row(0, 0, 0)
    forward_z_flights = [T, mul(Q(2, 3), T), mul(Q(4, 9), T), mul(Q(16, 9), T),
                         mul(Q(1, 2), minus(S, mul(4, T))),
                         mul(Q(2, 9), minus(mul(8, T), S)),
                         mul(Q(1, 9), minus(mul(10, S), mul(8, T)))]
    forward_n_flights = [T, mul(Q(2, 3), T), mul(Q(4, 9), T), mul(Q(16, 9), T),
                         mul(2, T), mul(8, T)]
    test_z, test_n = mul(2, plus(*forward_z_flights)), mul(2, plus(*forward_n_flights))
    require(test_z == row(0, Q(50, 9), Q(25, 9)), 'double forward Z duration')
    require(test_n == row(0, Q(250, 9), 0), 'double forward N duration')
    update_coefficients = {}
    for name, scale, shift in [('increment', Q(1, 2), Q(1, 40)),
                                ('decrement', Q(2), Q(-1, 20))]:
        # Scaling acts on original t; translation acts on the scaled target.
        update_coefficients[name] = 2 * (1 + scale) + 2 * scale * (1 + 1 / (1 - shift))
    inc, dec = update_coefficients['increment'], update_coefficients['decrement']
    require((inc, dec) == (Q(196, 39), Q(290, 21)), 'independent update duration reconstruction')
    pos = dec + test_n[1]
    X, Y = T, S  # From here coordinates are OUTPUT (D,x-prime,y-prime).
    input_a_inc = minus(mul(2, X), mul(Q(1, 20), D))
    input_a_pos = plus(mul(Q(1, 2), X), mul(Q(1, 40), D))
    input_b_inc = minus(mul(Q(39, 20), D), mul(2, Y))
    input_b_pos = minus(mul(Q(21, 40), D), mul(Q(1, 2), Y))
    require(plus(mul(Q(1, 2), input_a_inc), mul(Q(1, 40), D)) == X, 'A inc inverse')
    require(minus(mul(2, input_a_pos), mul(Q(1, 20), D)) == X, 'A dec inverse')
    require(minus(D, plus(mul(Q(1, 2), input_b_inc), mul(Q(1, 40), D))) == Y, 'B inc inverse')
    require(minus(D, minus(mul(2, input_b_pos), mul(Q(1, 20), D))) == Y, 'B dec inverse')
    durations = {
        'A increment': plus(mul(2, D), mul(inc, input_a_inc)),
        'A conditional, zero': test_z,
        'A conditional, positive decrement': plus(mul(2, D), mul(pos, input_a_pos)),
        'B increment': plus(mul(4, D), mul(inc, input_b_inc)),
        'B conditional, zero': plus(mul(2, D), mul(test_z[1], minus(D, Y)), mul(test_z[2], minus(D, X))),
        'B conditional, positive decrement': plus(mul(4, D), mul(pos, input_b_pos)),
    }
    counts = [4 + 10, 2 * len(forward_z_flights), 2 * len(forward_n_flights) + 4 + 10,
              3 + 4 + 10 + 3, 3 + 2 * len(forward_z_flights) + 3,
              3 + 2 * len(forward_n_flights) + 4 + 10 + 3]
    stated_core = table(proof, '| Core branch c |')
    require(len(stated_core) == 6, 'six core rows')
    for source_row, (name, duration), count in zip(stated_core, durations.items(), counts):
        require(source_row[0] == name and tuple(map(Q, source_row[1:4])) == duration,
                'source duration row: ' + name)
        require(int(source_row[4]) == count, 'source core event count: ' + name)

    # Static guard coverage on closed supersets of the encoded bands.
    guard_vertices = []
    for operation, scale, shift, hi in [('increment', Q(1, 2), Q(1, 40), Q(3, 20)),
                                       ('decrement', Q(2), Q(-1, 20), Q(1, 10))]:
        for t, s in itertools.product([Q(1, 20), hi], [Q(17, 20), Q(19, 20)]):
            scaled, final = scale * t, scale * t + shift
            hidden = scaled / (1 - shift)
            require(all(0 < v < s < 1 for v in (t, scaled, hidden, final)), 'update guard vertex')
            guard_vertices.append(dict(operation=operation, t=t, spectator=s, scaled=scaled,
                                       hidden=hidden, final=final))
    require(Q(17, 20) - 4 * Q(3, 20) == Q(1, 4), 'zero lower margin')
    require(8 * Q(3, 20) - Q(19, 20) == Q(1, 4), 'zero upper margin')
    require(Q(17, 20) - 8 * Q(1, 10) == Q(1, 20), 'positive margin')

    # Source-declared stationary words, now in positive gaps (a,b,c).
    a, b, c = row(1, 0, 0), row(0, 1, 0), row(0, 0, 1)
    positions = {'L': ZERO, 'X': a, 'Y': plus(a, b), 'R': plus(a, b, c)}
    order = {label: i for i, label in enumerate(positions)}
    words = {'LX': ['L', 'X', 'L'], 'LY': ['L', 'X', 'Y', 'X', 'L'],
             'RX': ['R', 'Y', 'X', 'Y', 'R'], 'RY': ['R', 'Y', 'R'],
             'LR': ['L', 'X', 'Y', 'R'], 'RL': ['R', 'Y', 'X', 'L'],
             'full': ['L', 'X', 'Y', 'R', 'Y', 'X', 'L']}
    lengths = {}
    source_words = table(proof, '| Primitive | Contact word |')
    require(len(source_words) == 7, 'seven stationary primitive rows')
    for name, source_row in zip(words, source_words):
        word = words[name]
        require(source_row[1].split(',') == word[1:], 'source contact word: ' + name)
        expected_lengths = []
        for start, end in zip(word, word[1:]):
            require(abs(order[end] - order[start]) == 1, 'flight joins adjacent markers')
            sign = 1 if order[end] > order[start] else -1
            length = mul(sign, minus(positions[end], positions[start]))
            require(positive_on_gaps(length), 'strict positive flight on entire ordered section')
            expected_lengths.append(length)
        parsed_lengths = [dict(a=a, b=b, c=c)[v] for v in source_row[2].split(',')]
        require(parsed_lengths == expected_lengths, 'source length list: ' + name)
        require(int(source_row[4]) == len(expected_lengths), 'source primitive count')
        lengths[name] = expected_lengths
    contact_gaps = {}
    for point in positions:
        contact_gaps[point] = {}
        for other in positions:
            if point == other:
                continue
            sign = 1 if order[other] > order[point] else -1
            gap = mul(sign, minus(positions[other], positions[point]))
            require(positive_on_gaps(gap), 'all three noncontact markers separated')
            contact_gaps[point][other] = gap
    require(set(lengths['full']) == {a, b, c}, 'mandatory word detects each boundary gap')

    # Independently instantiate the rule SCHEMA, then check its prescribed words.
    # No configuration state or next-collision calculation is performed.
    speeds, rules, branch_certificates = {}, {}, {}
    marker = {'L': 'L', 'X': 'X_0', 'Y': 'Y', 'R': 'R'}
    distances = {'LX': X, 'LY': Y, 'RX': minus(D, X), 'RY': minus(D, Y)}
    added_magnitudes = set()
    source_padding = table(proof, '| Branch | Left loops, in order |')
    source_ledger = table(proof, '| Branch | Core events | Target-loop events |')

    def label(name, speed):
        require(name not in speeds or speeds[name] == speed, 'fixed label speed')
        speeds[name] = Q(speed)
        return name

    def rule(incoming, at, outgoing):
        key = incoming + '|' + marker[at]
        value = dict(incoming=[incoming, marker[at]], outgoing=[outgoing, marker[at]])
        require(key not in rules or rules[key] == value, 'deterministic local input')
        require(speeds[incoming] != 0 and speeds[outgoing] != 0, 'distinct moving and stationary speeds')
        rules[key] = value

    for branch_index, ((branch, duration), core_count) in enumerate(zip(durations.items(), counts)):
        alpha, beta, gamma = duration
        coeff = {'LX': max(-beta, 0), 'LY': max(-gamma, 0),
                 'RY': max(gamma, 0), 'RX': max(beta, 0)}
        k = Q(30) - alpha - coeff['RX'] - coeff['RY'] - 4
        require(k > 0, 'strict positive final delay coefficient')
        left = [(p, 2 / Q(coeff[p])) for p in ('LX', 'LY') if coeff[p]]
        right = [(p, 2 / Q(coeff[p])) for p in ('RY', 'RX') if coeff[p]]
        sequence = [('full', Q(1))] + left + [('LR', Q(1))] + right + [('RL', Q(1)), ('full', 2 / k)]
        added_magnitudes.update(v for _, v in left + right + [('full', 2 / k)])
        source_row = source_padding[branch_index]
        format_loops = lambda items: ', '.join(f'{p}({coeff[p]})' for p, _ in items) or 'none'
        require(source_row[1:3] == [format_loops(left), format_loops(right)], 'source padding loops')
        require(Q(source_row[3]) == k and Q(source_row[4]) == 2 / k, 'source padding residual')
        prefix = 'branch_' + str(branch_index)
        specs = []
        for occurrence, (primitive, magnitude) in enumerate(sequence):
            word = words[primitive]
            direction = 1 if word[0] == 'L' else -1
            out = label(f'{prefix}/p{occurrence}/out', direction * magnitude)
            inward = None if primitive in ('LR', 'RL') else label(f'{prefix}/p{occurrence}/in', -direction * magnitude)
            specs.append(dict(primitive=primitive, word=word, magnitude=magnitude, out=out, inward=inward))
        next_instruction = label(prefix + '/next_instruction', 1)
        require(speeds[specs[0]['out']] == 1 and specs[0]['primitive'] == 'full', 'real inherited +1 entry')
        branch_time = ZERO
        branch_events = []
        for occurrence, spec in enumerate(specs):
            primitive, word = spec['primitive'], spec['word']
            q_next = specs[occurrence + 1]['out'] if occurrence + 1 < len(specs) else next_instruction
            if occurrence + 1 < len(specs):
                require(word[-1] == specs[occurrence + 1]['word'][0], 'same physical anchor at phase join')
            out, inward, magnitude = spec['out'], spec['inward'], spec['magnitude']
            if inward is None:
                for at in word[1:-1]:
                    rule(out, at, out)
                rule(out, word[-1], q_next)
            else:
                halfway = (len(word) - 1) // 2
                for at in word[1:halfway]:
                    rule(out, at, out)
                    rule(inward, at, inward)
                rule(out, word[halfway], inward)
                rule(inward, word[-1], q_next)
            # Verify local labels, signed displacement, and all interface contacts
            # against the independently listed finite word, with symbolic gaps.
            for event_index, (start, end, distance) in enumerate(zip(word, word[1:], lengths[primitive]), 1):
                current = out if inward is None or event_index <= (len(word) - 1) // 2 else inward
                expected_next = (q_next if event_index == len(word) - 1 else
                                 inward if inward is not None and event_index == (len(word) - 1) // 2 else current)
                key = current + '|' + marker[end]
                require(rules[key]['outgoing'] == [expected_next, marker[end]], 'complete local-rule realization')
                flight_duration = mul(1 / magnitude, distance)
                require(mul(speeds[current], flight_duration) == minus(positions[end], positions[start]), 'static flight equation')
                require(positive_on_gaps(flight_duration), 'strict time separation')
                branch_events.append(dict(occurrence=occurrence, start=start, contact=end,
                                          incoming=current, outgoing=expected_next,
                                          duration_in_gaps=flight_duration))
            # Independent affine duration from actual primitive distances.
            if primitive == 'full':
                dt = mul(2 / magnitude, D)
            elif primitive in ('LR', 'RL'):
                dt = mul(1 / magnitude, D)
            else:
                dt = mul(2 / magnitude, distances[primitive])
            branch_time = plus(branch_time, dt)
        require(plus(duration, branch_time) == mul(30, D), 'exact complementary padding identity')
        padding_events = len(branch_events)
        require(padding_events <= 26, 'general padding event bound')
        stated = source_ledger[branch_index]
        require(int(stated[1]) == core_count and int(stated[3]) == 18 and
                int(stated[4]) == padding_events and int(stated[5]) == core_count + padding_events,
                'source full event ledger')
        branch_certificates[branch] = dict(core_time_output_coordinates=duration,
            padding_time_output_coordinates=branch_time, k=k, primitive_sequence=sequence,
            core_events=core_count, padding_events=padding_events, total_events=core_count + padding_events,
            entry_label=specs[0]['out'], next_instruction=next_instruction, static_word_certificate=branch_events)

    old_magnitudes = {Q(v) for v in ['1', '1/3', '1/79', '1/41', '3/2', '1/4', '4', '1/2', '2']}
    require(len(old_magnitudes) == 9 and len(added_magnitudes) == 10, 'magnitude cardinalities')
    require(old_magnitudes.isdisjoint(added_magnitudes), 'no duplicate added magnitudes')
    common_speeds = {Q(0)} | old_magnitudes | added_magnitudes | {-v for v in old_magnitudes | added_magnitudes}
    require(len(common_speeds) == 39, 'common speed set cardinality')
    require(set(speeds.values()) <= common_speeds, 'all local rules use common speed set')
    require(max(r['total_events'] for r in branch_certificates.values()) == 54, 'actual maximum event count')
    require(min(r['k'] for r in branch_certificates.values()) == Q(1, 6), 'minimum padding residual')
    require(len(rules) == sum(r['padding_events'] for r in branch_certificates.values()), 'one rule per counted contact occurrence')
    result = dict(status='PASS', method='source-bound exact static rational certificate; no simulation',
        clock_proof_sha256=CLOCK_SHA, clock_manifest_sha256=MANIFEST_SHA, core_proof_sha256=CORE_SHA,
        checker_sha256=digest(read_bytes(Path(__file__))), source_members=source_hashes,
        source_anchors=anchors, reconstructed_update_coefficients=update_coefficients,
        forward_test_sums={'Z': plus(*forward_z_flights), 'N': plus(*forward_n_flights)},
        output_coordinate_rows=durations, core_event_counts=counts, encoded_guard_vertices=guard_vertices,
        exact_padding_guard='a=x>0, b=y-x>0, c=D-y>0; no additional inequalities',
        contact_gaps=contact_gaps, primitive_words=words, primitive_lengths=lengths,
        branch_certificates=branch_certificates, local_rules=list(rules.values()), label_speeds=speeds,
        padding_rule_count=len(rules), padding_phase_and_endpoint_label_count=len(speeds),
        new_positive_magnitudes=sorted(added_magnitudes), common_speeds=sorted(common_speeds),
        maximum_instruction_events=54, live_population=5,
        nonhalting_section_time='30*n*D, n >= 0, D > 0',
        halt_scope='designated section; optional three later identity crossings are post-halt',
        limits=['Dependency core is read and algebraically reconstructed, not formally reproved in full.',
                'Finite-table extension and nonaccumulation follow from the supplied mathematical argument.',
                '39 is the size of the stated common sufficient set, not a lower bound per program.',
                'No novelty, priority, exhaustive-search, optimization, or noise-robustness conclusion.'])
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(normalized(result), indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'PASS', 'output': str(output), 'rules': len(rules),
                      'speeds': len(common_speeds), 'maximum_events': 54}, sort_keys=True))


if __name__ == '__main__':
    main()
