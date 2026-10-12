"""Portable fresh source audit for the final Euler/group terminal extension.

Run against the integrated overlay, for example:
  python tools/audit_native.py --fast-root /path/to/ProveIt/.../fast \
      --output /tmp/euler_group_native.json --packets /tmp/euler_group_packets

The default audit independently replays every canonical, group and deferred
positive, and compares literal Regina cuts where the expansion cap permits.
These are coverage and correctness observations, not speed measurements.
"""

import argparse
from collections import Counter
from contextlib import nullcontext
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import time


PACKAGE = Path(__file__).resolve().parents[1]
OVERLAY = ('core_handlebody.py', 'normal_cut_handlebodies.py',
           'bundle_boundary_kernel.py', 'bundle_boundary_kernel_verify.py')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_hashes(fast):
    return {p.name: digest(p) for p in sorted((fast/'fastunknot').glob('*.py'))}


def worker(kind, fast, runtime):
    sys.path.insert(0, str(fast))
    if runtime is not None:
        sys.path.insert(0, str(runtime))
    from fastunknot.integer_codec import encoded_integer, json_safe
    case = json.load(sys.stdin)
    if kind == 'oracle':
        from normal_orbit_research.fixtures import regina_surface, regina_triangulation
        coordinates = [[encoded_integer(x) for x in row] for row in case['coordinates']]
        if sum(sum(row) for row in coordinates) > 4096:
            answer = dict(status='NOT_ATTEMPTED_EXPANSION_CAP', normal_disks_cap=4096)
        else:
            triangulation = regina_triangulation(case['triangulation'])
            surface = regina_surface(triangulation, coordinates)
            cut = surface.cutAlong()
            pieces = cut.triangulateComponents()
            genera = [p.recogniseHandlebody() for p in pieces]
            histogram = Counter(genera)
            answer = dict(status='COMPLETE', tetrahedra=cut.size(), components=len(pieces),
                          histogram=[dict(genus=g, multiplicity=n)
                                     for g, n in sorted(histogram.items())])
    else:
        from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
        from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
        result = normal_cut_handlebodies(case['triangulation'], case['coordinates'],
            record_certificate=True, forest_strategy='deferred')
        answer = dict(status=result['status'], reason=result.get('reason'),
                      stats=result.get('stats'))
        if result['status'] == 'COMPLETE':
            replayed = verify_normal_cut_handlebodies(case['triangulation'],
                case['coordinates'], result['certificate'])
            if not replayed:
                raise ArithmeticError('deferred positive failed independent source replay')
            raw = json.dumps(json_safe(result['certificate']), sort_keys=True).encode()
            answer.update(independent_replay=True, histogram=result['census']['histogram'],
                          certificate_sha256=hashlib.sha256(raw).hexdigest(),
                          certificate_bytes=len(raw), schema=result['certificate']['schema'])
    print(json.dumps(json_safe(answer)))


def call_worker(kind, case, fast, runtime=None, timeout=None):
    command = [sys.executable, str(Path(__file__).resolve()), '--worker', kind,
               '--fast-root', str(fast)]
    if runtime is not None:
        command += ['--runtime', str(runtime)]
    completed = subprocess.run(command, input=json.dumps(case), capture_output=True,
                               text=True, cwd=fast, timeout=timeout)
    if completed.returncode:
        raise RuntimeError(kind + ' worker failed: ' + completed.stderr)
    answer = json.loads(completed.stdout)
    if 'histogram' in answer:
        from fastunknot.integer_codec import encoded_integer
        answer['histogram'] = [dict(genus=encoded_integer(row['genus']),
                                    multiplicity=encoded_integer(row['multiplicity']))
                                for row in answer['histogram']]
    return answer


def replay_only(fast, directory, output):
    sys.path.insert(0, str(fast))
    from fastunknot.normal_cut_groups_verify import verify_normal_cut_group_handlebodies
    records = []
    packet_paths = sorted(directory.glob('*.json'))
    if not packet_paths:
        raise ValueError('no JSON source packets found in ' + str(directory))
    for path in packet_paths:
        packet = json.loads(path.read_text())
        source, certificate = packet['source'], packet['certificate']
        valid = verify_normal_cut_group_handlebodies(source['triangulation'],
            source['coordinates'], certificate)
        if not valid:
            raise ArithmeticError('saved source packet failed: ' + str(path))
        records.append(dict(file=path.name, source_id=source['id'], sha256=digest(path), verified=True))
    result = dict(mode='replay_only', passed=True, packets=len(records), records=records,
                  source_sha256=source_hashes(fast))
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(passed=True, packets=len(records))))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast-root', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--packets', type=Path)
    parser.add_argument('--replay-only', type=Path, metavar='PACKET_DIRECTORY')
    parser.add_argument('--oracle-timeout', type=float, default=20)
    parser.add_argument('--skip-oracle', action='store_true')
    parser.add_argument('--skip-deferred', action='store_true')
    parser.add_argument('--limit', type=int)
    parser.add_argument('--resume', action='store_true',
                        help='resume a partial --output after checking source and fixture hashes')
    parser.add_argument('--worker', choices=('oracle', 'deferred'), help=argparse.SUPPRESS)
    parser.add_argument('--runtime', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    fast = args.fast_root.resolve()
    if args.worker:
        worker(args.worker, fast, args.runtime)
        return
    if args.output is None:
        parser.error('--output is required')
    if args.replay_only:
        replay_only(fast, args.replay_only.resolve(), args.output)
        return
    if args.limit is not None and args.limit <= 0:
        parser.error('--limit must be positive')
    sys.path.insert(0, str(fast))
    from fastunknot.integer_codec import json_safe
    from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    from fastunknot.normal_cut_groups import normal_cut_group_handlebodies
    from fastunknot.normal_cut_groups_verify import verify_normal_cut_group_handlebodies
    try:
        import regina
        regina_version = regina.versionString()
    except ImportError:
        if not args.skip_oracle:
            raise
        regina_version = None
    pins = source_hashes(fast)
    cases, fixture_pins = [], {}
    for filename, group in [('corpus.json', 'historical'),
                            ('three_handle_corpus.json', 'interior_extension')]:
        path = PACKAGE/'fixtures'/filename
        fixture_pins[filename] = digest(path)
        cases.extend((group, c) for c in json.loads(path.read_text())['cases'])
    if args.limit is not None:
        cases = cases[:args.limit]
    if args.packets:
        args.packets.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    provenance = dict(source_sha256=pins, fixture_sha256=fixture_pins,
        deferred_overlay_sha256={n: digest(PACKAGE/'comparison/deferred'/n) for n in OVERLAY},
        python=sys.version, platform=platform.platform(), regina=regina_version,
        started_utc=datetime.now(timezone.utc).isoformat(),
        timing_claim='none: concurrent coverage/replay audit, not a benchmark')
    try:
        provenance['repository_commit'] = subprocess.run(['git', '-C', str(fast), 'rev-parse', 'HEAD'],
            check=True, capture_output=True, text=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        provenance['repository_commit'] = None
    counts, records, elapsed_before = Counter(), [], 0.0
    if args.resume:
        previous = json.loads(args.output.read_text())
        if previous['finished']:
            parser.error('--resume requires an incomplete audit')
        for key in ('source_sha256', 'fixture_sha256', 'deferred_overlay_sha256'):
            if previous['provenance'][key] != provenance[key]:
                raise ArithmeticError('cannot resume after ' + key + ' changed')
        records = previous['cases']
        if [c['id'] for c in records] != [c['id'] for _, c in cases[:len(records)]]:
            raise ArithmeticError('partial audit is not the expected fixture prefix')
        counts = Counter(previous['counts'])
        elapsed_before = previous['elapsed_audit_seconds']
        provenance['initial_started_utc'] = previous['provenance']['started_utc']
        provenance['resumed_after_cases'] = len(records)
        provenance['resume_note'] = ('Prior completed cases retain their independent replays; '
            'remaining cases run afresh against identical production, fixtures and deferred files.')
    start = time.perf_counter()
    context = tempfile.TemporaryDirectory(prefix='proveit-deferred-audit-') if not args.skip_deferred else nullcontext(None)
    with context as temp:
        runtime = Path(temp) if temp is not None else None
        if runtime is not None:
            shutil.copytree(fast/'fastunknot', runtime/'fastunknot',
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
            for filename in OVERLAY:
                shutil.copy2(PACKAGE/'comparison/deferred'/filename, runtime/'fastunknot'/filename)
        initial_records = len(records)
        for i, (family, case) in enumerate(cases):
            if i < initial_records:
                continue
            record = dict(id=case['id'], family=family)
            for name, producer, verifier in (
                    ('canonical', normal_cut_handlebodies, verify_normal_cut_handlebodies),
                    ('group', normal_cut_group_handlebodies, verify_normal_cut_group_handlebodies)):
                result = producer(case['triangulation'], case['coordinates'], record_certificate=True)
                item = dict(status=result['status'], reason=result.get('reason'), stats=result.get('stats'))
                if 'second_betti_sum' in result:
                    item['second_betti_sum'] = result['second_betti_sum']
                counts[name + '/' + result['status']] += 1
                counts[family + '/' + name + '/' + result['status']] += 1
                if result['status'] == 'COMPLETE':
                    if not verifier(case['triangulation'], case['coordinates'], result['certificate']):
                        raise ArithmeticError(name + ' independent replay failed on ' + case['id'])
                    encoded = json.dumps(json_safe(result['certificate']), sort_keys=True).encode()
                    item.update(independent_replay=True, histogram=result['census']['histogram'],
                        schema=result['certificate']['schema'], certificate_bytes=len(encoded),
                        certificate_sha256=hashlib.sha256(encoded).hexdigest())
                    counts[name + '/independent_replays'] += 1
                    if name == 'group' and args.packets:
                        path = args.packets/(case['id'].replace('/', '__') + '.json')
                        path.write_text(json.dumps(json_safe(dict(source=case,
                            certificate=result['certificate'])), indent=2)+'\n')
                        item['packet'] = path.name
                record[name] = item
            if runtime is not None:
                record['deferred'] = call_worker('deferred', case, fast, runtime)
                counts['deferred/' + record['deferred']['status']] += 1
                counts[family + '/deferred/' + record['deferred']['status']] += 1
                if record['deferred']['status'] == 'COMPLETE':
                    counts['deferred/independent_replays'] += 1
            winners = [record[name]['histogram'] for name in ('canonical', 'group', 'deferred')
                       if name in record and record[name]['status'] == 'COMPLETE']
            if winners and any(h != winners[0] for h in winners):
                raise ArithmeticError('native census disagreement on ' + case['id'])
            group_ok = record['group']['status'] == 'COMPLETE'
            canonical_ok = record['canonical']['status'] == 'COMPLETE'
            record['canonical_plus_group'] = 'COMPLETE' if canonical_ok or group_ok else 'INCONCLUSIVE'
            counts['canonical_plus_group/' + record['canonical_plus_group']] += 1
            if group_ok and not canonical_ok:
                counts['group/new_vs_canonical'] += 1
            if runtime is not None:
                deferred_ok = record['deferred']['status'] == 'COMPLETE'
                if canonical_ok and not deferred_ok:
                    raise ArithmeticError('deferred path lost canonical positive on ' + case['id'])
                record['deferred_plus_group'] = 'COMPLETE' if deferred_ok or group_ok else 'INCONCLUSIVE'
                counts['deferred_plus_group/' + record['deferred_plus_group']] += 1
                if group_ok and not deferred_ok:
                    counts['group/new_vs_deferred'] += 1
            if not args.skip_oracle:
                try:
                    oracle = call_worker('oracle', case, fast, timeout=args.oracle_timeout)
                except subprocess.TimeoutExpired:
                    oracle = dict(status='TIMEOUT', timeout_seconds=args.oracle_timeout)
                record['regina'] = oracle
                counts['regina/' + oracle['status']] += 1
                if oracle['status'] == 'COMPLETE':
                    for name in ('canonical', 'group', 'deferred'):
                        if name in record and record[name]['status'] == 'COMPLETE':
                            if oracle['histogram'] != record[name]['histogram']:
                                raise ArithmeticError(name + ' disagrees with Regina on ' + case['id'])
                            counts[name + '/regina_agreements'] += 1
                    if winners:
                        counts['union/regina_agreements'] += 1
            records.append(record)
            report = dict(finished=False, counts=counts, provenance=provenance,
                          elapsed_audit_seconds=elapsed_before + time.perf_counter() - start,
                          cases=records)
            args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')
            if (i + 1) % 10 == 0 or (group_ok and not canonical_ok):
                print(json.dumps(dict(done=i + 1, id=case['id'], counts=counts)), flush=True)
    if source_hashes(fast) != pins:
        raise ArithmeticError('production sources changed during source audit')
    report.update(finished=True, elapsed_audit_seconds=elapsed_before + time.perf_counter() - start)
    args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')
    print(json.dumps(dict(finished=True, counts=counts)), flush=True)


if __name__ == '__main__':
    main()
