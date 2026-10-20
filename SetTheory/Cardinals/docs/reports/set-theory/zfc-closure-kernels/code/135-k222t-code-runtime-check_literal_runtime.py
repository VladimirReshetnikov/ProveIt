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
table_bytes = args.table.read_bytes()
site_bytes = args.sites.read_bytes()
table = s.r.table(args.table)
sites = json.loads(site_bytes)
working = {q for q, b in table}
assert args.states > 0 and all(q >= 0 for q in working)
starts = [int(line.split()[-1]) for line in table_bytes.decode('ascii').splitlines()
          if line.startswith('#! start ')]
assert starts == [95], ('Expected the legacy start declaration', starts)
assert len(working) == args.states and len(table) == 2 * args.states
assert 95 in working and 96 in working and 254 not in working
assert set(table) == {(q, b) for q in working for b in (0, 1)}
assert {n for w, d, n in table.values()} - working == {254}
reachable, pending = {95}, [95]
for state in pending:
    for bit in (0, 1):
        target = table[state, bit][2]
        if target != 254 and target not in reachable:
            reachable.add(target)
            pending.append(target)
assert reachable == working, ('Unreachable declared states', sorted(working - reachable))
# Generic syntax validation does not replace the independent logical source
# calibration. It prevents a partial, duplicate, or malformed leaf list from
# being accepted as a complete source-program runtime certificate.
assert isinstance(sites, list) and sites
leaves, prefixes = set(), set()
for site in sites:
    assert isinstance(site, list) and len(site) == 3, ('Malformed source row', site)
    pc, op, arg = site
    assert isinstance(pc, str) and 0 < len(pc) <= 64 and set(pc) <= {'0', '1'}
    assert pc not in leaves, ('Duplicate source address', pc)
    assert op in ('CI', 'CD', 'CB', 'CC', 'CH'), ('Unknown primitive', op)
    if op in ('CI', 'CD'):
        assert type(arg) is int and 0 <= arg < 9
    elif op in ('CB', 'CC'):
        assert type(arg) is int and arg >= 1
    else:
        assert arg is None
    leaves.add(pc)
    prefixes.update(pc[:i] for i in range(len(pc)))
assert not leaves.intersection(prefixes), 'A source leaf is a prefix of another leaf'
assert len(prefixes) == len(leaves) - 1
assert all(p + bit in leaves or p + bit in prefixes
           for p in prefixes for bit in ('0', '1')), 'Incomplete binary source tree'
assert [row[0] for row in sites] == sorted(leaves), 'Source leaves are not in left-to-right order'
case_path = args.output.with_name(args.output.stem + '_cases.json')
assert len({p.resolve() for p in (args.table, args.sites, args.output, case_path)}) == 4
EXPECTED = len(sites) + sum(1 for x in sites if x[1] == 'CD')
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
assert len(cases) == EXPECTED
assert rows == set(table), ('Incomplete transition coverage', sorted(set(table) - rows))
assert args.table.read_bytes() == table_bytes and args.sites.read_bytes() == site_bytes, 'Inputs changed during proof'
case_bytes = (json.dumps(cases, indent=2) + '\n').encode('utf-8')
# Save the bound case record first; a successful top-level receipt is emitted
# only after its companion file exists in full.
case_path.write_bytes(case_bytes)
result = {'status': 'UNIVERSAL_MATHEMATICAL_PASS', 'working_states': len(working),
          'transition_rows': len(table), 'cases': len(cases),
          'symbolic_steps': sum(c['symbolic_steps'] for c in cases),
          'minimum_actual_steps': min(c['duration'][0] for c in cases),
          'table_sha256': hashlib.sha256(table_bytes).hexdigest(),
          'sites_sha256': hashlib.sha256(site_bytes).hexdigest(),
          'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'engine_sha256': hashlib.sha256(Path(s.__file__).read_bytes()).hexdigest(),
          'helper_sha256': hashlib.sha256(Path(s.r.__file__).read_bytes()).hexdigest(),
          'seconds': time.monotonic() - started, 'blocks': blocks,
          'directly_used_rows': sorted(rows),
          'all_transition_rows_exercised': True,
          'complete_source_prefix_tree': True,
          'graph_reachable_states': len(reachable),
          'cases_file': case_path.name,
          'cases_sha256': hashlib.sha256(case_bytes).hexdigest(),
          'scope': 'All guarded source leaves, all natural primary values, arbitrary natural gap and first spare, arbitrary finite spare tail, and whole zero tape exterior. Exact supplied table. Ordinary mathematical checker, not a proof-assistant endpoint.'}
args.output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ('blocks', 'directly_used_rows')}, indent=2))

