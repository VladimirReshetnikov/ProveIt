"""Profile one complete group-terminal query including saved-JSON replay.

This is bottleneck diagnosis, not a benchmark.  cProfile changes execution
costs; its timings must not replace the separately measured query medians.
Imports and fixture loading occur outside the single profiled query.
"""

import argparse
from collections import defaultdict
import cProfile
import hashlib
import io
import json
from pathlib import Path
import platform
import pstats
import sys
import time


PACKAGE = Path(__file__).resolve().parents[1]
NEW_MODULES = {'source_cut_group.py', 'source_cut_group_verify.py',
               'free_group_elimination.py', 'free_group_elimination_verify.py',
               'normal_cut_groups.py', 'normal_cut_groups_verify.py'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast-root', type=Path, required=True)
    parser.add_argument('--case', default='pachner23_5_8_2/mixed')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    fast = args.fast_root.resolve()
    sys.path.insert(0, str(fast))
    from fastunknot.integer_codec import json_safe, encoded_integer
    from fastunknot.normal_cut_groups import normal_cut_group_handlebodies
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    bank = []
    for filename in ('corpus.json', 'three_handle_corpus.json'):
        bank.extend(json.loads((PACKAGE/'fixtures'/filename).read_text())['cases'])
    case = next((c for c in bank if c['id'] == args.case), None)
    if case is None:
        parser.error('unknown fixture ID: ' + args.case)
    tri = case['triangulation']
    coords = [[encoded_integer(x) for x in row] for row in case['coordinates']]
    phases, result, raw = {}, None, None

    def query():
        nonlocal result, raw
        start = time.perf_counter()
        result = normal_cut_group_handlebodies(tri, coords, record_certificate=True)
        phases['producer'] = time.perf_counter() - start
        if result['status'] != 'COMPLETE':
            raise ArithmeticError('selected query did not produce a complete certificate')
        start = time.perf_counter()
        raw = json.dumps(json_safe(result['certificate']), sort_keys=True,
                         separators=(',', ':')).encode()
        reloaded = json.loads(raw)
        phases['json_serialization_and_loading'] = time.perf_counter() - start
        start = time.perf_counter()
        if not verify_normal_cut_handlebodies(tri, coords, reloaded):
            raise ArithmeticError('independent dispatch replay failed')
        phases['independent_source_and_group_replay'] = time.perf_counter() - start

    profiler = cProfile.Profile()
    wall_start = time.perf_counter()
    profiler.runcall(query)
    wall_seconds = time.perf_counter() - wall_start
    stats = pstats.Stats(profiler)
    functions, module_self = [], defaultdict(float)
    classes = defaultdict(float)
    for (filename, line, function), (primitive, total, own, cumulative, callers) in stats.stats.items():
        name = Path(filename).name
        if str(fast) in filename:
            display = str(Path(filename).relative_to(fast))
            category = 'new_terminal_modules' if name in NEW_MODULES else 'inherited_native_modules'
        elif filename == str(Path(__file__).resolve()):
            display, category = 'tools/profile_terminal.py', 'profiling_driver'
        else:
            display, category = filename, 'python_runtime_and_libraries'
        module_self[display] += own
        classes[category] += own
        functions.append(dict(file=display, line=line, function=function,
            primitive_calls=primitive, total_calls=total,
            self_seconds=own, cumulative_seconds=cumulative))
    functions.sort(key=lambda row: row['cumulative_seconds'], reverse=True)
    wanted = {
        ('normal_parallelity.py', 'normal_cut_parallelity'),
        ('parallelity_boundary_moments.py', '_compile'),
        ('normal_cut_groups.py', '_group_terminal'),
        ('normal_parallelity_verify.py', 'verify_normal_cut_parallelity'),
        ('parallelity_boundary_moments_verify.py', 'verify_parallelity_moment_words'),
        ('source_cut_group.py', 'compile_disk_cut_presentation'),
        ('source_cut_group_verify.py', 'verify_disk_cut_presentation'),
        ('free_group_elimination.py', 'certify_free_group'),
        ('free_group_elimination_verify.py', 'replay_free_group'),
        ('interval_orbits.py', '_count_orbits'),
        ('interval_orbit_verify.py', 'verify_orbit_certificate'),
        ('interval_orbits.py', '_contract'),
        ('weighted_orbit_verify.py', '_prefix_events'),
        ('weighted_orbit_verify.py', '_translation_fold'),
    }
    selected = [row for row in functions
                if (Path(row['file']).name, row['function']) in wanted]
    certificate_fields = {key: len(json.dumps(json_safe(value), sort_keys=True,
        separators=(',', ':')).encode()) for key, value in result['certificate'].items()}
    report = dict(case=case['id'], status='COMPLETE', independent_replay=True,
        scope='one producer + compact JSON save/load + existing independent dispatch replay',
        interpretation='cProfile diagnostic only; not a replacement for unprofiled benchmark medians',
        python=sys.version, platform=platform.platform(),
        source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in sorted((fast/'fastunknot').glob('*.py'))},
        profile_wall_seconds=wall_seconds, profiled_phase_wall_seconds=phases,
        profile_total_self_seconds=stats.total_tt,
        total_calls=stats.total_calls, primitive_calls=stats.prim_calls,
        certificate_bytes=len(raw), certificate_field_bytes=certificate_fields,
        native_stats=result['stats'], histogram=result['census']['histogram'],
        exclusive_self_seconds_by_category=dict(classes),
        exclusive_self_seconds_by_module=dict(sorted(module_self.items(),
            key=lambda row: row[1], reverse=True)),
        selected_function_costs=selected, functions=functions,
        cumulative_cost_warning='Cumulative function costs overlap and must not be summed across nested calls.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')
    stream = io.StringIO()
    pstats.Stats(profiler, stream=stream).sort_stats('cumulative').print_stats(55)
    pstats.Stats(profiler, stream=stream).sort_stats('tottime').print_stats(35)
    text_path = args.output.with_suffix('.txt')
    heading = ('ONE-QUERY cProfile DIAGNOSTIC, NOT A BENCHMARK\n'
               + json.dumps(dict(case=case['id'], phase_seconds=phases,
                                  certificate_bytes=len(raw)), indent=2) + '\n\n')
    text_path.write_text(heading + stream.getvalue())
    print(json.dumps(dict(case=case['id'], profile_wall_seconds=wall_seconds,
        phases=phases, selected=selected, category_self_seconds=dict(classes),
        certificate_bytes=len(raw)), indent=2))


if __name__ == '__main__':
    main()
