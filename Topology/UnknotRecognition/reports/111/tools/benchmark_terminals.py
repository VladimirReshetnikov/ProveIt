"""Complete-query measurements with shuffled arms and duplicated A/A control.

Native measurements include source construction, certificate production,
JSON serialization/deserialization and independent source replay. Regina
measurements include source import, literal cut, component recognition and
JSON serialization. Imports and one warm-up per arm are outside timings.
Coverage refusals are retained; no speed ratio is formed for unlike verdicts.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
import sys
import time

PACKAGE = Path(__file__).resolve().parents[1]


def worker(args):
    sys.path.insert(0, str(Path(args.fast_root).resolve()))
    import regina
    from fastunknot.integer_codec import json_safe, encoded_integer
    from fastunknot.normal_cut_groups import normal_cut_group_handlebodies
    from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    from normal_orbit_research.fixtures import regina_surface, regina_triangulation
    case = json.load(sys.stdin)
    coords = [[encoded_integer(x) for x in row] for row in case['coordinates']]
    tri = case['triangulation']

    def native(method):
        if method.startswith('group'):
            result = normal_cut_group_handlebodies(tri, coords, record_certificate=True)
        else:
            result = normal_cut_handlebodies(tri, coords,
                group_fallback=(method == 'portfolio'), record_certificate=True)
        if result['status'] != 'COMPLETE':
            return dict(status=result['status'], reason=result.get('reason'))
        raw = json.dumps(json_safe(result['certificate']), sort_keys=True,
                         separators=(',', ':')).encode()
        reloaded = json.loads(raw)
        if not verify_normal_cut_handlebodies(tri, coords, reloaded):
            raise ArithmeticError('native independent replay failed')
        answer = dict(status='COMPLETE', histogram=result['census']['histogram'],
                      certificate_bytes=len(raw))
        if method.startswith('group'):
            answer['presentation'] = result['stats']['terminal']['presentation']
        return answer

    def oracle():
        imported = regina_triangulation(tri)
        surface = regina_surface(imported, coords)
        cut = surface.cutAlong()
        histogram = Counter(piece.recogniseHandlebody() for piece in cut.triangulateComponents())
        answer = dict(status='COMPLETE', histogram=[dict(genus=g, multiplicity=n)
                       for g, n in sorted(histogram.items())], literal_tetrahedra=cut.size())
        json.dumps(answer, sort_keys=True)
        return answer

    arms = ['canonical', 'group_A', 'group_B', 'portfolio']
    normal_disks = sum(map(sum, coords))
    if normal_disks <= args.oracle_disk_cap:
        arms.append('regina')
    call = lambda name: oracle() if name == 'regina' else native(name)
    warmups = {name: call(name) for name in arms}
    positive_histograms = [json.dumps(json_safe(r['histogram']), sort_keys=True)
                           for r in warmups.values() if r['status'] == 'COMPLETE']
    if len(set(positive_histograms)) > 1:
        raise ArithmeticError('unmatched output genera')
    rng = random.Random(20261012)
    samples = {name: [] for name in arms}
    orders = []
    for _ in range(args.rounds):
        order = arms[:]
        rng.shuffle(order)
        orders.append(order)
        for name in order:
            start = time.perf_counter_ns()
            got = call(name)
            seconds = (time.perf_counter_ns() - start) / 1e9
            if got != warmups[name]:
                raise ArithmeticError('nonrepeatable answer')
            samples[name].append(seconds)
    result = dict(id=case['id'], tetrahedra=len(tri['tetrahedra']),
        normal_disks=normal_disks, coordinate_max_bits=max((x.bit_length() for row in coords for x in row), default=0),
        rounds=args.rounds, orders=orders,
        arms={name: dict(**warmups[name], seconds=samples[name],
                        median_seconds=statistics.median(samples[name]),
                        min_seconds=min(samples[name]), max_seconds=max(samples[name])) for name in arms},
        oracle_status='COMPLETE' if 'regina' in arms else 'NOT_ATTEMPTED_EXPANSION_CAP',
        python=sys.version, regina=regina.versionString(), platform=platform.platform())
    print(json.dumps(json_safe(result)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast-root', required=True)
    parser.add_argument('--output')
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--oracle-disk-cap', type=int, default=4096)
    parser.add_argument('--case-timeout', type=float, default=45.0)
    parser.add_argument('--case-id', action='append', help='Only run this exact case; repeatable')
    parser.add_argument('--worker', action='store_true')
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    if args.worker:
        worker(args)
        return
    if not args.output:
        parser.error('--output is required')
    fast = Path(args.fast_root).resolve()
    sys.path.insert(0, str(fast))
    from fastunknot.integer_codec import json_safe
    from normal_orbit_research.fixtures import layered_torus
    bank = json.loads((PACKAGE/'fixtures/corpus.json').read_text())['cases']
    cases = [x for x in bank if x['id'] in {'pilot/finite_trefoil/0', 'pilot/finite_figureEight/0',
                                           'pachner23_5_8_2/mixed'}]
    tri, primitive = layered_torus(1)
    for copies in [1, 8, 64, 512, 1024]:
        cases.append(dict(id=f'meridian_copies/{copies}', triangulation=tri,
                          coordinates=[[copies*x for x in row] for row in primitive]))
    for bits in [128, 500, 16384]:
        cases.append(dict(id=f'meridian_binary/{bits}', triangulation=tri,
                          coordinates=[[x*(1 << bits) for x in row] for row in primitive]))
    if args.case_id:
        requested = set(args.case_id)
        selected = [case for case in cases if case['id'] in requested]
        if {case['id'] for case in selected} != requested:
            parser.error('Unknown --case-id')
        cases = selected
    sources = {str(p.relative_to(fast)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in sorted((fast/'fastunknot').glob('*.py'))}
    report = dict(methodology=__doc__, random_seed=20261012, rounds=args.rounds,
                  oracle_disk_cap=args.oracle_disk_cap, case_timeout_seconds=args.case_timeout,
                  source_sha256=sources, cases=[])
    output = Path(args.output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [sys.executable, str(Path(__file__).resolve()), '--worker', '--fast-root', str(fast),
               '--rounds', str(args.rounds), '--oracle-disk-cap', str(args.oracle_disk_cap)]
    for case in cases:
        try:
            run = subprocess.run(command, input=json.dumps(json_safe(case)), text=True,
                                 capture_output=True, timeout=args.case_timeout)
            if run.returncode:
                raise RuntimeError(run.stderr)
            row = json.loads(run.stdout)
        except subprocess.TimeoutExpired:
            row = dict(id=case['id'], status='CASE_TIMEOUT', seconds=args.case_timeout)
        report['cases'].append(row)
        output.write_text(json.dumps(report, indent=2) + '\n')
        print(case['id'], 'complete' if 'arms' in row else row['status'], flush=True)
    if sources != {str(p.relative_to(fast)): hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in sorted((fast/'fastunknot').glob('*.py'))}:
        raise ArithmeticError('source changed during benchmark')


if __name__ == '__main__':
    main()
