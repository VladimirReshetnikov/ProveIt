#!/usr/bin/env python3
"""Replay the inherited symbolic runtime rules on a native K-labelled table.

Requires an extracted K221_Construction_2026-10-20 directory. Only Python's
standard library is needed. This proves the primitive implementation, not the
source program's equiconsistency theorem or its blank-tape initialization.
"""
from pathlib import Path
import argparse, hashlib, json, sys, time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_table(path):
    table, starts = {}, []
    for line in path.read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        elif line and not line.startswith('#'):
            q, bit, write, direction, target = line.split()
            q, bit, write, target = map(int, (q, bit, write, target))
            assert (q, bit) not in table
            assert bit in (0, 1) and write in (0, 1) and direction in ('L', 'R')
            table[q, bit] = write, 1 if direction == 'R' else -1, target
    working = {q for q, bit in table}
    assert starts == [0] and 0 in working and 254 not in working
    assert set(table) == {(q, bit) for q in working for bit in (0, 1)}
    assert {target for write, direction, target in table.values()} - working == {254}
    return table


def validate_sites(sites):
    assert isinstance(sites, list) and sites
    leaves, prefixes = set(), set()
    for row in sites:
        assert isinstance(row, list) and len(row) == 3
        pc, op, arg = row
        assert isinstance(pc, str) and 0 < len(pc) <= 64 and set(pc) <= {'0', '1'}
        assert pc not in leaves and op in ('CI', 'CD', 'CB', 'CC', 'CH')
        if op == 'CH':
            assert arg is None
        elif op in ('CI', 'CD'):
            assert type(arg) is int and 0 <= arg < 9
        else:
            assert type(arg) is int and arg >= 1
        leaves.add(pc)
        prefixes.update(pc[:i] for i in range(len(pc)))
    assert not (leaves & prefixes)
    assert all(p + bit in leaves | prefixes for p in prefixes for bit in ('0', '1'))
    assert len(prefixes) == len(leaves) - 1
    assert [row[0] for row in sites] == sorted(leaves)
    return dict(leaf_count=len(leaves), maximum_depth=max(map(len, leaves)),
                complete_binary_tree=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', type=Path, required=True,
                    help='extracted K221_Construction_2026-10-20 directory')
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--sites', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True,
                    help='receipt JSON; companion cases JSON is also written')
    args = ap.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Assertions are required; disable -O/PYTHONOPTIMIZE.')
    runtime = args.baseline.resolve() / 'portable/runtime'
    vendor = runtime / 'vendor'
    mapping_path = runtime / 'reference_results/legacy_mapping.json'
    assert (vendor / 'symbolic_runtime.py').is_file()
    assert (vendor / 'independent_runtime.py').is_file()
    sys.path.insert(0, str(vendor))
    import symbolic_runtime as rt

    native = read_table(args.table)
    sites = json.loads(args.sites.read_text())
    source_validation = validate_sites(sites)
    mapping = {int(q): int(v) for q, v in json.loads(mapping_path.read_text()).items()}
    needed = {q for q, bit in native} | {254}
    extensions = {q: q + 1000 for q in needed if q not in mapping}
    mapping.update(extensions)
    assert needed <= mapping.keys() and len({mapping[q] for q in needed}) == len(needed)
    assert mapping[84] == 96 and mapping[254] == 254
    table = {(mapping[q], bit): (w, d, mapping[target])
             for (q, bit), (w, d, target) in native.items()}
    expected = sum(2 if row[1] == 'CD' else 1 for row in sites)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    cases_path = args.output.with_name(args.output.stem + '_cases.json')
    start = time.monotonic()
    common = dict(table_sha256=digest(args.table), sites_sha256=digest(args.sites),
                  mapping_sha256=digest(mapping_path), driver_sha256=digest(Path(__file__)),
                  checker_sha256=digest(vendor / 'symbolic_runtime.py'),
                  helper_sha256=digest(vendor / 'independent_runtime.py'),
                  working_states=len(native) // 2, input_validation=source_validation,
                  expected_cases=expected, legacy_mapping_extensions=extensions)
    cases, used = [], set()

    def fail(stage, exc, **context):
        report = dict(common, status='NOT_PROVED', stage=stage, reason=repr(exc),
                      prior_cases=len(cases), seconds=time.monotonic() - start, **context)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(report, sort_keys=True), flush=True)
        return 1

    try:
        lemmas, blocks = rt.prove_blocks(table)
    except (AssertionError, KeyError) as exc:
        return fail('block_lemmas', exc)
    print('All four exact-table block lemmas proved.', flush=True)
    for index, site in enumerate(sites):
        for positive in ((False, True) if site[1] == 'CD' else (False,)):
            try:
                result = rt.case(table, lemmas, site, positive)
            except (AssertionError, KeyError) as exc:
                return fail('primitive', exc, site_index=index, site=site, positive=positive)
            used.update(result.pop('rows'))
            result.pop('trace')
            cases.append(dict(site_index=index, positive=positive, **result))
            if len(cases) % 1000 == 0:
                print('Proved', len(cases), 'of', expected, 'cases.', flush=True)
    assert len(cases) == expected
    report = dict(common, status='UNIVERSAL_MATHEMATICAL_PASS', cases=len(cases),
                  symbolic_steps=sum(case['symbolic_steps'] for case in cases),
                  minimum_actual_steps=min(case['duration'][0] for case in cases),
                  seconds=time.monotonic() - start, blocks=blocks,
                  directly_used_legacy_rows=sorted(used), cases_data_file=cases_path.name,
                  scope='All independent natural primary values at each decrement guard, arbitrary natural additional gap, arbitrary first spare value and arbitrary finite remaining spare list, and the complete zero exterior. Executable mathematical induction; not a proof-assistant kernel certificate.',
                  loop_bounds_scope='The 4000-iteration bound limits proof construction only. It imposes no bound on actual runtime, register values, gap, or spare-list length.',
                  separate_obligations=['blank-tape initialization', 'source-program logical calibration'])
    cases_path.write_text(json.dumps(cases, separators=(',', ':')) + '\n')
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ('blocks', 'directly_used_legacy_rows')}, indent=2), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
