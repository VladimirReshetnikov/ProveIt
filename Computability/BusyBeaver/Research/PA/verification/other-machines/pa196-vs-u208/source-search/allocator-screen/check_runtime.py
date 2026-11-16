#!/usr/bin/env python3
"""Rederive every arbitrary-value primitive contract for a literal candidate.

Place the unchanged Joint-U209 symbolic_runtime.py and independent_runtime.py
beside this file. No saved contract result is assumed by this verification.
"""
import argparse
import gzip
import hashlib
import json
import sys
import time
from pathlib import Path

PINS = {
    'symbolic_runtime.py': '61b9c66272e8fd149829177cc384013814aea3c6b3b6b6f48e462d3913ea2022',
    'independent_runtime.py': 'd490397a2b31be4f7f62461a3d9bcd88faf9093de904e43eea1b865561e7b7ee',
}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path, expected_states):
    table = {}; starts = []
    for line in Path(path).read_text().splitlines():
        if line.startswith('#! start '): starts.append(int(line[9:]))
        if not line or line.startswith('#'): continue
        q, b, w, d, z = line.split(); q, b, w, z = map(int, (q, b, w, z))
        need((q, b) not in table and b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'Bad transition')
        table[q, b] = (w, 1 if d == 'R' else -1, z)
    states = {q for q, b in table}
    need(starts == [74] and 74 in states and 254 not in states, 'Start/halt convention')
    need(len(states) == expected_states and set(table) == {(q, b) for q in states for b in (0, 1)}, 'Census')
    need({z for w, d, z in table.values()} - states == {254}, 'Undefined target')
    return table, states

def verify(machine, sites_path, mapping_path, output, expected_states=208):
    need(__debug__ and not sys.flags.optimize, 'Run without Python -O or PYTHONOPTIMIZE')
    here = Path(__file__).resolve().parent
    for name, digest in PINS.items(): need(sha(here / name) == digest, 'Runtime engine identity: ' + name)
    import symbolic_runtime as s
    table, states = read(machine, expected_states)
    sites = json.loads(Path(sites_path).read_text())
    mapping = {int(k): int(v) for k, v in json.loads(Path(mapping_path).read_text()).items()}
    for q in states | {254}: mapping.setdefault(q, q + 1000)
    need(len({mapping[q] for q in states | {254}}) == len(states) + 1, 'Noninjective state conjugacy')
    inverse = {mapping[q]: q for q in states | {254}}
    literal = {(mapping[q], b): (w, d, mapping[z]) for (q, b), (w, d, z) in table.items()}
    need(mapping[84] == 96 and mapping[254] == 254 and s.HEADER_BASE == 56, 'Frame or dispatcher mismatch')
    start = time.monotonic(); lemmas, blocks = s.prove_blocks(literal)
    cases = []; used = set()
    for index, site in enumerate(sites):
        for positive in ((False, True) if site[1] == 'CD' else (False,)):
            try:
                answer = s.case(literal, lemmas, site, positive)
            except Exception as e:
                raise RuntimeError(f'case {index} {site} positive={positive}: {e}') from e
            used.update(answer['rows'])
            answer['rows'] = sorted((inverse[q], b) for q, b in answer['rows'])
            answer.pop('trace')
            cases.append(dict(site_index=index, positive=positive, **answer))
        if (index + 1) % 1000 == 0:
            print(f'Rederived {len(cases)} arbitrary-value contracts', flush=True)
    for block in blocks:
        for event in block['trace']: used.add(tuple(event[1][:2]))
    need(len(cases) == sum(2 if site[1] == 'CD' else 1 for site in sites) and used <= set(literal), 'Source, case or row coverage')
    need(all(len(c['duration']) == 13 and c['duration'][0] > 0 and all(n >= 0 for n in c['duration'])
             for c in cases), 'Nonpositive affine duration')
    report = dict(status='FULL_UNIVERSAL_RUNTIME_PASS', working_states=len(states),
                  transition_rows=len(table), source_primitives=len(sites), cases=len(cases),
                  row_coverage=len(used), symbolic_inferences=sum(c['symbolic_steps'] for c in cases),
                  minimum_duration_constant=min(c['duration'][0] for c in cases),
                  all_duration_coefficients_nonnegative=True, arbitrary_primary_registers=9,
                  arbitrary_natural_gap=True, arbitrary_nonempty_finite_spares=True,
                  header_base=56, blocks=blocks, blocks_use_legacy_labels=True,
                  legacy_to_native=inverse, native_sha256=sha(machine), source_sha256=sha(sites_path),
                  engine_sha256=PINS, seconds=time.monotonic()-start,
                  scope='Executable induction over arbitrary unary runs and finite lists; no proof-assistant kernel certificate.')
    output = Path(output); output.mkdir(parents=True, exist_ok=True)
    (output / 'runtime.json').write_text(json.dumps(report, indent=2) + '\n')
    with gzip.GzipFile(filename=str(output / 'runtime_cases.json.gz'), mode='wb', mtime=0) as f:
        f.write((json.dumps(cases, separators=(',', ':')) + '\n').encode())
    return report

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--machine', type=Path, required=True)
    p.add_argument('--sites', type=Path, required=True)
    p.add_argument('--mapping', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--expected-states', type=int, default=208)
    a = p.parse_args()
    r = verify(a.machine, a.sites, a.mapping, a.output, a.expected_states)
    print(json.dumps({k: v for k, v in r.items() if k not in ('blocks', 'legacy_to_native')}, indent=2))
