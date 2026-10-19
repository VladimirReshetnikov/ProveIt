"""Full unbounded source/runtime check of a supplied inherited-label table.

Use only with an independently calibrated exact sites file. This script verifies
the binary instruction interface and literal table census, not that calibration.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time
import symbolic_runtime as s

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--table', type=Path, required=True)
ap.add_argument('--sites', type=Path, required=True)
ap.add_argument('--states', type=int, required=True)
ap.add_argument('--output', type=Path, required=True)
args = ap.parse_args()
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled')
table = s.r.table(args.table)
sites = json.loads(args.sites.read_text())
working = {q for q, b in table}
assert len(working) == args.states and len(table) == 2 * args.states
assert 95 in working and 96 in working and 254 not in working
assert set(table) == {(q, b) for q in working for b in (0, 1)}
assert {n for w, d, n in table.values()} - working == {254}
assert hashlib.sha256(args.sites.read_bytes()).hexdigest() == '1ebe9691507b2d3236951a31d6b9a7ef548a2cdf90525cd57051992f8ac2626f'
assert len(sites) == 6455
lemmas, blocks = s.prove_blocks(table)
print('Literal census and all four unbounded block schemas pass.', flush=True)
started = time.monotonic()
cases, rows = [], set()
args.output.parent.mkdir(parents=True, exist_ok=True)
for index, site in enumerate(sites):
    for positive in ((False, True) if site[1] == 'CD' else (False,)):
        try:
            answer = s.case(table, lemmas, site, positive)
        except (AssertionError, KeyError) as error:
            result = {'status': 'NOT_PROVED', 'site_index': index, 'site': site,
                      'positive': positive, 'prior_cases': len(cases), 'reason': str(error),
                      'seconds': time.monotonic() - started}
            args.output.write_text(json.dumps(result, indent=2) + '\n')
            print(json.dumps(result, indent=2), flush=True)
            raise SystemExit(1)
        rows.update(answer.pop('rows'))
        answer.pop('trace')
        cases.append({'site_index': index, 'positive': positive, **answer})
        if len(cases) % 1000 == 0:
            print('proved', len(cases), 'guards', round(time.monotonic() - started, 2), 'seconds', flush=True)
assert len(cases) == 8386
assert rows == set(table), "Every literal row must be covered"
result = {'status': 'UNIVERSAL_MATHEMATICAL_PASS', 'working_states': len(working),
          'transition_rows': len(table), 'cases': len(cases),
          'symbolic_steps': sum(c['symbolic_steps'] for c in cases),
          'minimum_actual_steps': min(c['duration'][0] for c in cases),
          'table_sha256': hashlib.sha256(args.table.read_bytes()).hexdigest(),
          'sites_sha256': hashlib.sha256(args.sites.read_bytes()).hexdigest(),
          'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'engine_sha256': hashlib.sha256(Path(s.__file__).read_bytes()).hexdigest(),
          'helper_sha256': hashlib.sha256(Path(s.r.__file__).read_bytes()).hexdigest(),
          'seconds': time.monotonic() - started, 'blocks': blocks,
          'directly_used_rows': sorted(rows),
          'scope': 'All guarded source leaves, all natural primary values, arbitrary natural gap and first spare, arbitrary finite spare tail, and whole zero tape exterior. Exact supplied table. Ordinary mathematical checker, not a proof-assistant endpoint.'}
args.output.write_text(json.dumps(result, indent=2) + '\n')
args.output.with_name(args.output.stem + '_cases.json').write_text(json.dumps(cases, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ('blocks', 'directly_used_rows')}, indent=2))
