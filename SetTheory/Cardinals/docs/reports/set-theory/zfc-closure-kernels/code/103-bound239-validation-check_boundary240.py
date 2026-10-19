"""Emit and check the explicitly repaired 240-state boundary-reassociated table.

The extra projector state is charged. This is not a sub-240-state solution.
"""
from pathlib import Path
import hashlib
import json
import sys
import time
import symbolic_runtime as s

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Run with assertions enabled')
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'boundary240'
OUT.mkdir(exist_ok=True)
source = ROOT / 'source_encoding' / 'boundary239_provisional2_old.tm'
table = s.r.table(source)
assert 223 not in {q for q, _ in table}
assert table[218, 0] == (0, -1, 86)
table[218, 0] = (0, -1, 223)
table[223, 0] = (0, 1, 16)
table[223, 1] = (1, 1, 99)
assert len(table) == 480
literal = '#! start 95\n' + ''.join(
    f'{q} {b} {w} {"R" if d == 1 else "L"} {n}\n'
    for (q, b), (w, d, n) in sorted(table.items()))
table_path = OUT / 'boundary240_old.tm'
table_path.write_text(literal)
sites_path = ROOT / 'formalism' / 'extra' / 'boundary224_sites.json'
sites = json.loads(sites_path.read_text())
assert hashlib.sha256(sites_path.read_bytes()).hexdigest() == '7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
assert sites == json.loads((ROOT / 'source_encoding' / 'boundary239_sites.json').read_text())
(OUT / 'sites_logical.json').write_bytes(sites_path.read_bytes())

# The projector macro restores the original intended endpoints in three steps
# for every possible left tag, with an arbitrary tape outside those two cells.
for tag, endpoint in [(0, 23), (1, 105)]:
    q, head, tape = 218, 0, {-1: tag, 0: 0}
    for tick in range(3):
        w, direction, next_q = table[q, tape[head]]
        tape[head] = w
        head += direction
        q = next_q
    assert (q, head, tape) == (endpoint, 1, {-1: tag, 0: 0})

# Exact blank initialization to the same complete known root tape.
target_record = json.loads((ROOT / 'validation' / 'baseline_literal_checks.json').read_text())
q, head, tape = 95, 0, set()
for tick in range(409691):
    w, direction, q1 = table[q, int(head in tape)]
    if w:
        tape.add(head)
    else:
        tape.discard(head)
    head += direction
    q = q1
assert (q, head, tape) == (96, -5, set(target_record['one_cells']))

lemmas, blocks = s.prove_blocks(table)
print('Exact projector, complete blank root, and four unbounded block schemas pass.', flush=True)
started = time.monotonic()
rows, cases = set(), []
for i, site in enumerate(sites):
    for positive in ((False, True) if site[1] == 'CD' else (False,)):
        try:
            answer = s.case(table, lemmas, site, positive)
        except (AssertionError, KeyError) as error:
            result = {'status': 'NOT_PROVED', 'site_index': i, 'site': site,
                      'positive': positive, 'prior_cases': len(cases),
                      'reason': str(error)}
            (OUT / 'universal_runtime.json').write_text(json.dumps(result, indent=2) + '\n')
            print(json.dumps(result, indent=2))
            raise SystemExit(1)
        rows.update(answer.pop('rows'))
        answer.pop('trace')
        cases.append({'site_index': i, 'positive': positive, **answer})
        if len(cases) % 1000 == 0:
            print('proved', len(cases), 'guards', round(time.monotonic() - started, 2), 'seconds', flush=True)
assert len(cases) == 8386
result = {
    'status': 'UNIVERSAL_MATHEMATICAL_PASS',
    'working_states': 240,
    'transition_rows': 480,
    'table_sha256': hashlib.sha256(table_path.read_bytes()).hexdigest(),
    'sites_sha256': hashlib.sha256(sites_path.read_bytes()).hexdigest(),
    'provisional_source_table_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'repair': {'changed_218_read0': [0, 'L', 223],
               'added_223_read0': [0, 'R', 16], 'added_223_read1': [1, 'R', 99],
               'extra_working_states_charged': 1,
               'three_step_projector': {'left_tag0_endpoint': [23, 1],
                                        'left_tag1_endpoint': [105, 1]}},
    'blank_steps_to_exact_root': 409691,
    'cases': len(cases),
    'symbolic_steps': sum(c['symbolic_steps'] for c in cases),
    'minimum_actual_steps': min(c['duration'][0] for c in cases),
    'seconds': time.monotonic() - started,
    'blocks': blocks,
    'directly_used_rows': sorted(rows),
    'scope': 'Unbounded whole-tape instruction runtime for the repaired240 table and certified boundary224 source; ordinary mathematical checker, not proof-assistant endpoint. This table does not improve the state bound.'
}
(OUT / 'universal_runtime.json').write_text(json.dumps(result, indent=2) + '\n')
(OUT / 'universal_runtime_cases.json').write_text(json.dumps(cases, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ('blocks', 'directly_used_rows')}, indent=2))
