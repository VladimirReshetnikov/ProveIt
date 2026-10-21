#!/usr/bin/env python3
"""Independent finite table, renaming, blank-prefix and local-macro audit.

Python 3.10+, standard library only. Run from any directory. This script does
not prove the source calibration or its unbounded primitive implementation;
those are separate obligations in the enclosing research packet.
"""
from pathlib import Path
from hashlib import sha256
import argparse, gzip, json

HERE = Path(__file__).resolve().parent
NATIVE_HALT, START, STEPS = 254, 0, 95674
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)

def digest(data):
    return sha256(data).hexdigest()

def dump(path, obj):
    path.write_text(json.dumps(obj, indent=2) + '\n', encoding='utf-8')

def parse(raw):
    out = {}
    for lineno, line in enumerate(raw.decode('ascii').splitlines(), 1):
        if not line or line.startswith('#'):
            continue
        fields = line.split()
        assert len(fields) == 5, (lineno, fields)
        q, read, write, direction, target = fields
        q, read, write, target = map(int, (q, read, write, target))
        assert q >= 0 and target >= 0 and read in (0, 1) and write in (0, 1)
        assert direction in ('L', 'R')
        assert (q, read) not in out, ('Duplicate row', q, read)
        out[q, read] = write, -1 if direction == 'L' else 1, target
    return out

def serialize(table, start, halt):
    header = f'#! start {start}\n#! halt {halt}\n'
    rows = ''.join(f'{q} {b} {w} {"R" if d == 1 else "L"} {z}\n'
                   for (q, b), (w, d, z) in sorted(table.items()))
    return (header + rows).encode('ascii')

def simulate(table, steps, rename=None):
    # A sparse dictionary is deliberately separate from the C++ ordered-set
    # implementation. Zeros are absent. No frame detector selects the endpoint.
    tape, q, h, low, high, trace = {}, START, 0, 0, 0, []
    working = {a for a, _ in table}
    for tick in range(steps):
        assert q in working, ('Premature halt', tick, q)
        b = tape.get(h, 0)
        w, d, z = table[q, b]
        trace.append([q, h, b, w, d, z])
        if w:
            tape[h] = 1
        else:
            tape.pop(h, None)
        q, h = z, h + d
        low, high = min(low, h), max(high, h)
    return {'steps': steps, 'state': q, 'head': h, 'one_cells': sorted(tape),
            'head_min': low, 'head_max': high}, trace

def expected_seed():
    head, gap = -8, 1
    logical = [4, 0, 0, 0, 0, 0, 0, 0, 0]
    physical = [0] * 9
    for i, p in enumerate(PHY):
        physical[p] = logical[i]
    spares = [1] * 40
    header = head + 64 + gap
    ones, pos = {head - 1, header}, header + 1
    for value in physical + spares:
        pos += 1
        ones.update(range(pos, pos + value + 1))
        pos += value + 1
    return {'steps': STEPS, 'state': 84, 'head': head, 'header': header,
            'gap': gap, 'logical_registers': logical,
            'physical_registers': physical, 'spares': spares,
            'one_cells': sorted(ones)}

def local81(table):
    # The old rows below are pinned literal K217 rows. Only cells -1 and 0
    # are read or written. Cell 0 is known zero; cell -1 is arbitrary.
    old = {(81, 0): (0, -1, 92), (92, 0): (0, 1, 104),
           (92, 1): (1, 1, 107), (104, 0): (0, 1, 123),
           (107, 0): (0, 1, 21)}
    new_rows = {(81, 0): (0, -1, 111), (111, 0): (0, 1, 104),
                (111, 1): (1, 1, 128), (104, 0): (0, 1, 123),
                (128, 0): (0, 1, 21)}
    for k, v in new_rows.items():
        assert table[k] == v, ('Local-macro row mismatch', k, table[k], v)
    cases = []
    for left in (0, 1):
        endpoints = []
        for label, fragment in [('K217', old), ('K216', new_rows)]:
            tape = {-1: left, 0: 0}
            before = dict(tape)
            q, h, trace = 81, 0, []
            for _ in range(3):
                assert h in tape, 'Reads an unspecified cell'
                b = tape[h]
                w, d, z = fragment[q, b]
                trace.append([q, h, b, w, d, z])
                tape[h] = w
                q, h = z, h + d
            assert tape == before
            endpoints.append((q, h))
            cases.append({'left_bit': left, 'table': label, 'trace': trace,
                          'endpoint_state': q, 'endpoint_head': h,
                          'entire_tape_unchanged': True})
        assert endpoints[0] == endpoints[1] == ((123 if left == 0 else 21), 1)
    return {'status': 'EXACT_THREE_STEP_EQUIVALENCE', 'cases': cases,
            'premise': 'State 81, head h, tape[h]=0; all other tape cells arbitrary.',
            'conclusion': 'Both tables reach state 123 if tape[h-1]=0, otherwise state 21, at h+1 after exactly three transitions, leaving the entire tape unchanged.',
            'scope': 'Local replacement only; the complete table has additional source-decoder changes.'}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--directory', type=Path, default=HERE)
    a = ap.parse_args()
    out = a.directory
    raw = (out / 'k216.native.tm').read_bytes()
    T = parse(raw)
    states = {q for q, _ in T}
    assert len(states) == 216 and len(T) == 432
    assert all((q, b) in T for q in states for b in (0, 1))
    assert NATIVE_HALT not in states
    assert {z for _, _, z in T.values()} - states == {NATIVE_HALT}
    # Directed reachability counts only declared working states, not halting.
    reachable, pending = {START}, [START]
    for q in pending:
        for b in (0, 1):
            z = T[q, b][2]
            if z != NATIVE_HALT and z not in reachable:
                reachable.add(z)
                pending.append(z)
    assert reachable == states
    mapping = {q: i for i, q in enumerate(sorted(states))}
    mapping[NATIVE_HALT] = 216
    assert mapping[START] == 0
    C = {(mapping[q], b): (w, d, mapping[z]) for (q, b), (w, d, z) in T.items()}
    canonical = serialize(C, 0, 216)
    (out / 'k216.tm').write_bytes(canonical)
    assert parse(canonical) == C
    reverse = {z: q for q, z in mapping.items()}
    assert {(reverse[q], b): (w, d, reverse[z]) for (q, b), (w, d, z) in C.items()} == T
    dump(out / 'canonicalization.json', {
        'rule': 'Increasing native working-state labels map to 0 through 215; native halt 254 maps to 216.',
        'native_start': 0, 'canonical_start': 0,
        'native_halt': 254, 'canonical_halt': 216,
        'native_dispatch': 84, 'canonical_dispatch': mapping[84],
        'native_to_canonical': mapping,
        'native_sha256': digest(raw), 'canonical_sha256': digest(canonical)})
    endpoint, trace = simulate(T, STEPS)
    seed = expected_seed()
    assert all(endpoint[k] == seed[k] for k in ('steps', 'state', 'head', 'one_cells'))
    canonical_endpoint, canonical_trace = simulate(C, STEPS)
    assert canonical_endpoint['state'] == mapping[endpoint['state']]
    assert all(canonical_endpoint[k] == endpoint[k] for k in ('steps', 'head', 'one_cells', 'head_min', 'head_max'))
    assert canonical_trace == [[mapping[q], h, b, w, d, mapping[z]] for q, h, b, w, d, z in trace]
    trace_raw = (json.dumps({'columns': ['state','head','read','write','move','next'],
                            'steps': STEPS, 'initial': {'state':0,'head':0,'one_cells':[]},
                            'trace': trace, 'endpoint': endpoint}, separators=(',', ':')) + '\n').encode('ascii')
    (out / 'blank-prefix.json.gz').write_bytes(gzip.compress(trace_raw, mtime=0))
    dump(out / 'blank-seed.json', {**seed, 'head_min': endpoint['head_min'], 'head_max': endpoint['head_max'],
                                   'native_table_sha256': digest(raw),
                                   'trace_uncompressed_sha256': digest(trace_raw)})
    proof = local81(T)
    dump(out / 'local81-proof.json', proof)
    # A human-readable complete canonical transition table.
    tex = ['% Generated by audit.py from k216.tm; 216 working states plus halt H=216.',
           '\\begin{longtable}{rll}', '\\toprule',
           'State & Read 0 & Read 1 \\\\', '\\midrule', '\\endhead']
    for q in range(216):
        acts = []
        for bit in (0, 1):
            w, d, z = C[q, bit]
            acts.append(f'${w}\\,{"R" if d == 1 else "L"}\\,{"H" if z == 216 else str(z)}$')
        tex.append(f'{q} & {acts[0]} & {acts[1]} \\\\')
    tex += ['\\bottomrule', '\\end{longtable}', '']
    (out / 'full_table.tex').write_text('\n'.join(tex), encoding='ascii')
    cpp_checked = []
    for name, wanted in [('native', endpoint), ('canonical', canonical_endpoint)]:
        p = out / f'blank-cpp-{name}.json'
        if p.exists():
            assert json.loads(p.read_text()) == wanted, ('C++ replay mismatch', name)
            cpp_checked.append(name)
    report = {'status': 'PASS', 'separate_cpp_endpoints_checked': cpp_checked, 'working_states': 216, 'transition_rows': 432,
              'alphabet': [0, 1], 'blank_symbol': 0, 'tape': 'two-way infinite',
              'working_state_graph_reachable_from_start': len(reachable),
              'canonical_working_states': [0, 215], 'canonical_halt': 216,
              'blank_steps': STEPS, 'native_endpoint_state': endpoint['state'],
              'canonical_endpoint_state': canonical_endpoint['state'],
              'endpoint_head': endpoint['head'], 'one_cell_count': len(endpoint['one_cells']),
              'logical_registers': seed['logical_registers'], 'spare_count': len(seed['spares']),
              'spare_value': 1, 'gap': seed['gap'], 'head_min': endpoint['head_min'], 'head_max': endpoint['head_max'],
              'native_sha256': digest(raw), 'canonical_sha256': digest(canonical),
              'source_sha256': digest((out / 'sites216.json').read_bytes()),
              'trace_uncompressed_sha256': digest(trace_raw),
              'native_and_canonical_traces_correspond_step_for_step': True,
              'local81_exact_arbitrary_tape_equivalence': True,
              'scope': 'Finite literal initialization, table format, state renaming and local 81 macro only. Source calibration and the unbounded primitive theorem are separate.',
              'audit_script_sha256': digest(Path(__file__).read_bytes())}
    dump(out / 'audit.json', report)
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
