#!/usr/bin/env python3
"""Independent read-only audit of the marker215 saved proof and blank trace.

This does not rerun the universal induction checker. It independently binds
the stored ordered case census to the source, checks row coverage and affine
durations, compares the parent inventory, and replays every startup step in
native and dense form before parsing the complete final tape.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import sys

from compare_tables import parse


def check(b, message):
    if not b:
        raise ValueError(message)


def read_json(p):
    raw = p.read_bytes()
    return json.loads(gzip.decompress(raw) if p.suffix == '.gz' else raw)


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--candidate', type=Path, required=True)
    p.add_argument('--baseline', type=Path, required=True)
    p.add_argument('--mapping', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    c = a.candidate
    native = c / 'marker215.native.tm'
    dense = c / 'marker215.tm'
    source = c / 'sites.json'
    cases_path = c / 'runtime/runtime_cases.json'
    if not cases_path.exists():
        cases_path = c / 'runtime/runtime_cases.json.gz'
    boot_path = c / 'runtime/startup.json'
    if not boot_path.exists():
        boot_path = c / 'runtime/startup.json.gz'
    report_path = c / 'runtime/runtime.json'
    start, t = parse(native)
    dense_start, d = parse(dense)
    check(start == dense_start == 0 and len(t) == len(d) == 430, 'table census')
    check(digest(native) == 'e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252', 'native identity')
    check(digest(source) == '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba', 'source identity')
    m = {int(k): v for k, v in read_json(c / 'canonicalization.json')['native_to_dense'].items()}
    check(len(m) == len(set(m.values())) == 216 and m[0] == 0 and m[254] == 215, 'canonical bijection')
    check({(m[q], b): (w, direction, m[z]) for (q, b), (w, direction, z) in t.items()} == d, 'all-row renaming')

    rows = read_json(source)
    cases = read_json(cases_path)
    expected_order = [(i, b) for i, (_, op, _) in enumerate(rows)
                      for b in ((False, True) if op == 'CD' else (False,))]
    check([(x['site_index'], x['positive']) for x in cases] == expected_order, 'complete ordered guards')
    check(len(cases) == 6176, 'case count')
    for x in cases:
        check(len(x['duration']) == 13 and x['duration'][0] > 0, 'positive affine duration')
        check(all(type(z) is int and z >= 0 for z in x['duration']), 'nonnegative affine coefficients')
    legacy = {int(k): v for k, v in read_json(a.mapping).items()}
    for q in {q for q, b in t} | {254}:
        if q not in legacy:
            legacy[q] = q + 1000
    coverage = {tuple(x) for case in cases for x in case['rows']}
    check(coverage == {(legacy[q], b) for q, b in t}, 'exact full row coverage')
    report = read_json(report_path)
    check(report['status'] == 'UNIVERSAL_MATHEMATICAL_PASS' and not report['failures'], 'runtime status')
    check(report['table_sha256'] == digest(native) and report['sites_sha256'] == digest(source), 'runtime binding')

    parent_cases = read_json(a.baseline / 'verification/root-run1/runtime/runtime_cases.json.gz')
    check([(x['site_index'], x['positive']) for x in parent_cases] == expected_order, 'parent ordered guards')
    deltas = Counter()
    for old, new in zip(parent_cases, cases):
        check(old['duration'][1:] == new['duration'][1:] and old['motion'] == new['motion'], 'unchanged variable cost and motion')
        deltas[new['duration'][0] - old['duration'][0]] += 1
    check(deltas == Counter({0: 5632, 6: 416, 2: 128}), 'runtime differences')

    boot = read_json(boot_path)
    trace = boot['trace']
    check(len(trace) == boot['steps'] == 95714, 'blank trace length')
    q, h, ones = 0, 0, set()
    dq, dh, dense_ones = 0, 0, set()
    used = Counter()
    for k, event in enumerate(trace):
        check(len(event) == 6, 'trace event arity')
        sq, sh, bit, w, direction, z = event
        check((sq, sh, bit) == (q, h, int(h in ones)), 'native recorded configuration')
        check(t[q, bit] == (w, direction, z), 'native recorded action')
        db = int(dh in dense_ones)
        dw, dd, dz = d[dq, db]
        check((dq, dh, db, dw, dd, dz) == (m[q], h, bit, w, direction, m[z]), 'dense lockstep')
        used[q, bit] += 1
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        if dw:
            dense_ones.add(dh)
        else:
            dense_ones.discard(dh)
        q, h = z, h + direction
        dq, dh = dz, dh + dd
    check((q, h, sorted(ones)) == (boot['state'], boot['head'], boot['one_cells']), 'exact terminal support')
    check((dq, dh, dense_ones) == (m[q], h, ones), 'dense terminal tape')
    check(q == 84 and h == -8 and min(ones) == h - 1, 'dispatcher and zero left exterior')
    header = min(x for x in ones if x >= h)
    check(header == 57 and header - h - 64 == 1, 'header and gap')
    check(not (ones & set(range(h, header))), 'root instruction address')
    pos = header + 1
    values = []
    while pos <= max(ones):
        check(pos not in ones and pos + 1 in ones, 'unary block separator')
        first = pos + 1
        pos = first
        while pos in ones:
            pos += 1
        values.append(pos - first - 1)
    check(pos == max(ones) + 1 and len(values) == 49, 'complete finite block list')
    physical_order = (6, 2, 0, 4, 3, 7, 8, 5, 1)
    logical = [values[k] for k in physical_order]
    check(logical == boot['registers'] == [4, 0, 0, 0, 0, 0, 0, 0, 0], 'logical seed')
    check(values[9:] == boot['spares'] == [1] * 40, 'entire spare list')
    out = {
        'status': 'INDEPENDENT_SAVED_EVIDENCE_AND_WHOLE_BLANK_REPLAY_PASS',
        'working_states': 215, 'rows': 430, 'source_sites': len(rows),
        'ordered_guard_cases': len(cases), 'symbolic_rules': sum(x['symbolic_steps'] for x in cases),
        'minimum_duration_constant': min(x['duration'][0] for x in cases),
        'exact_covered_rows': len(coverage), 'parent_constant_differences': dict(sorted(deltas.items())),
        'blank_steps': len(trace), 'blank_one_cells': len(ones), 'header': header,
        'logical_registers': logical, 'spare_values': values[9:],
        'marker_zero_steps_in_blank_prefix': used[52, 0],
        'scope': 'Independent stored-census and literal blank audit; not a second universal induction algorithm.',
        'pins': {str(x): digest(x) for x in (native, dense, source, cases_path, boot_path, report_path, a.mapping, Path(__file__))}
    }
    a.output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k not in ('pins', 'spare_values')}, indent=2))


if __name__ == '__main__':
    main()
