"""Independent Regina cuts and handlebody recognition, with per-case time caps.

Run from fast/: python -m marked_parallelity_research.audit_census --output PATH
The oracle constructs an actual cut triangulation, separates its components,
and calls Regina's exact recogniseHandlebody on each. It does not reuse any
native core, genus, or attachment computation.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

from fastunknot.integer_codec import encoded_integer, json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.fixtures import regina_surface, regina_triangulation
from normal_orbit_research.seeds import sources


def oracle(case):
    coordinates = [[encoded_integer(n) for n in row] for row in case['coordinates']]
    if sum(sum(row) for row in coordinates) > 4096:
        return dict(status='NOT_ATTEMPTED_EXPANSION_CAP', normal_disks_cap=4096)
    triangulation = regina_triangulation(case['triangulation'])
    surface = regina_surface(triangulation, coordinates)
    cut = surface.cutAlong()
    values = [p.recogniseHandlebody() for p in cut.triangulateComponents()]
    counts = Counter(values)
    return dict(tetrahedra=cut.size(), components=len(values),
                histogram=[dict(genus=g, multiplicity=n) for g, n in sorted(counts.items())])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output')
    parser.add_argument('--oracle', action='store_true')
    parser.add_argument('--timeout', type=float, default=15)
    args = parser.parse_args()
    if args.oracle:
        print(json.dumps(oracle(json.load(sys.stdin))))
        return
    source_pins = sources()
    corpus_bytes = Path(__file__).with_name('corpus.json').read_bytes()
    bank = json.loads(corpus_bytes)
    results, counts = [], Counter()
    start = time.perf_counter()
    for index, case in enumerate(bank['cases']):
        initial = time.perf_counter()
        result = normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                                        record_certificate=True)
        record = dict(id=case['id'], native_status=result['status'],
                      native_reason=result.get('reason'), native_seconds=time.perf_counter() - initial)
        counts[result['status']] += 1
        if result['status'] != 'COMPLETE':
            counts['inconclusive_' + result['reason']] += 1
        if result['status'] == 'COMPLETE':
            assert verify_normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                                                  result['certificate'])
            encoded = json.dumps(json_safe(result['certificate']), sort_keys=True).encode()
            record.update(census=result['census'], certificate_bytes=len(encoded),
                          certificate_sha256=hashlib.sha256(encoded).hexdigest())
            counts['independent_replays'] += 1
        try:
            completed = subprocess.run([sys.executable, '-m',
                'marked_parallelity_research.audit_census', '--oracle'],
                input=json.dumps(case), text=True, capture_output=True, timeout=args.timeout)
            if completed.returncode:
                raise RuntimeError(completed.stderr)
            reference = json.loads(completed.stdout)
            record['regina'] = reference
            if reference.get('status') == 'NOT_ATTEMPTED_EXPANSION_CAP':
                counts['regina_expansion_cap'] += 1
            else:
                counts['regina_complete'] += 1
            if result['status'] == 'COMPLETE' and 'histogram' in reference:
                assert result['census']['histogram'] == reference['histogram'], record
                counts['certified_regina_agreements'] += 1
        except subprocess.TimeoutExpired:
            record['regina'] = dict(status='TIMEOUT', seconds=args.timeout)
            counts['regina_timeouts'] += 1
        results.append(record)
        if (index + 1) % 10 == 0:
            print(json.dumps(dict(done=index + 1, counts=counts)), flush=True)
    assert sources() == source_pins, 'native sources changed during audit'
    report = dict(source_revision=bank['source_revision'], counts=counts,
                  native_source_sha256=source_pins,
                  corpus_sha256=hashlib.sha256(corpus_bytes).hexdigest(),
                  seconds=time.perf_counter() - start, cases=results)
    Path(args.output).write_text(json.dumps(json_safe(report), indent=2) + '\n')
    print(json.dumps(dict(counts=counts, seconds=report['seconds'])), flush=True)


if __name__ == '__main__':
    main()
