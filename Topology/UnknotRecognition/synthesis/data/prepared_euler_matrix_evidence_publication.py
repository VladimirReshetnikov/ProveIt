"""Replay and bind the finite prepared-matrix/pivot-pilot evidence publication.

No solver discovery, tests, timing, PDF build, or historical publication main
is run.  Execute only after the final three build logs and pilot replay exist.
"""
from collections import Counter
from contextlib import contextmanager
from hashlib import sha256
import ast
import io
import json
from pathlib import Path
import re
import sys
import tarfile

from strict_pachner32_publication import included_tex, python_dependencies
import prepared_euler_matrix_publication as core
import prepared_euler_matrix_differential as differential

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
PREFIX = 'prepared-euler-evidence'
CORE_COMMIT = '4e152f0ef'
CORE_MANIFEST = DATA/'prepared-euler-matrix-publication.json'
CORE_MANIFEST_SHA256 = 'c7c36c2485f5e66229fd5339f950a86c8f7d01f3d0122e62f136cb04aabe69e9'
PREFLIGHT_SHA256 = {
    'prepared-euler-matrix-differential-preflight-failure.txt':
        '3c0b0e49264bc232a5bb7fd8065cf093d0ec71a85baf62178207fdf48108d41c',
    'prepared-euler-matrix-differential-preflight-source.txt':
        '23b62616612efccd8e90c24f46df4a99d1b228e4714cdea44b419594e41a9733',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def equal(actual, expected, message):
    require(differential.typed_equal(actual, expected), message)


def load(path):
    return json.loads(path.read_bytes())


def check_pins(pins):
    require(type(pins) is dict, 'pin map must be a dictionary')
    for name, expected in pins.items():
        require(type(name) is str and type(expected) is str, 'literal source pin')
        path = (ROOT/name).resolve()
        require(path.is_relative_to(ROOT) and path.is_file(), 'missing or escaping pinned path')
        require(digest(path) == expected, 'current file differs from pin: '+name)


def check_core():
    require(digest(CORE_MANIFEST) == CORE_MANIFEST_SHA256, 'core manifest changed')
    historical_bytes = differential.git('show', CORE_COMMIT+':'+differential.PREFIX+
                                        str(CORE_MANIFEST.relative_to(ROOT)))
    require(sha256(historical_bytes).hexdigest() == CORE_MANIFEST_SHA256,
            'core manifest is not the committed test checkpoint')
    manifest = load(CORE_MANIFEST)
    equal({key: manifest[key] for key in ('schema', 'passed', 'tests', 'test_modules',
        'skipped_tests', 'tested_files', 'native_modules')},
        dict(schema='prepared-euler-matrix-publication-v1', passed=True, tests=394,
             test_modules=44, skipped_tests=0, tested_files=361, native_modules=299),
        'exact core test coverage')
    snapshot_path = DATA/'prepared-euler-matrix-test-source.json'
    snapshot = load(snapshot_path)
    tested = core.test_source_files()
    equal(snapshot['expected_tests'], 394, 'pre-run test count')
    equal(snapshot['files_sha256'], tested, 'complete current pre-run test closure')
    require(len(tested) == 361, 'test source closure size')
    for name, value in tested.items():
        require(manifest['files_sha256'][name] == value, 'tested dependency differs from core')
    artifacts = {snapshot_path, DATA/'prepared-euler-matrix-tests.txt',
                 DATA/'prepared-euler-matrix-test-command.txt',
                 DATA/'prepared_euler_matrix_publication.py'}
    for path in artifacts:
        require(manifest['files_sha256'][str(path.relative_to(ROOT))] == digest(path),
                'test/core-helper artifact differs from committed core')
    test_log = (DATA/'prepared-euler-matrix-tests.txt').read_text()
    require(re.findall(r'^Ran (\d+) tests in [\d.]+s$', test_log, re.M) == ['394'] and
            test_log.rstrip().endswith('\nOK'), 'successful retained 394-test log')
    require(not re.search(r'skipped|expected failure|unexpected success|^FAIL|^ERROR',
                          test_log, re.I | re.M), 'no skipped or failed tests')
    native = differential.native_hashes()
    equal(native, {name: value for name, value in tested.items()
                   if name.startswith('fast/fastunknot/') and name.endswith('.py')},
          'complete native file set belongs to tested closure')
    return manifest, tested, artifacts | {CORE_MANIFEST}


def check_preflight():
    paths = {DATA/name for name in PREFLIGHT_SHA256}
    for path in paths:
        require(digest(path) == PREFLIGHT_SHA256[path.name], 'retained preflight artifact changed')
    failure = (DATA/'prepared-euler-matrix-differential-preflight-failure.txt').read_text()
    require('FileNotFoundError:' in failure and 'normal_orbit_research/__init__.py' in failure and
            'before, fixed_before = native_hashes(), fixed_hashes()' in failure,
            'documented namespace-package preflight failure')
    old = ast.parse((DATA/'prepared-euler-matrix-differential-preflight-source.txt').read_text())
    new = ast.parse((DATA/'prepared_euler_matrix_differential.py').read_text())
    for tree in (old, new):
        nodes = [node for node in tree.body if isinstance(node, ast.FunctionDef) and
                 node.name == 'fixed_hashes']
        require(len(nodes) == 1, 'one preflight pinning function')
        nodes[0].body = [ast.Pass()]
    require(ast.dump(old, include_attributes=False) == ast.dump(new, include_attributes=False),
            'preflight repair changed something beyond namespace pin handling')
    return dict(retained=True, kind='namespace_package_preflight', solver_queries_run=0,
                algorithm_failure=False, predeclared_cases_unchanged=True), paths


def check_historical(document, native):
    historical = document['historical']
    equal(historical['revision'], differential.REVISION, 'exact predecessor revision')
    archive = differential.git('archive', '--format=tar', differential.REVISION,
                               differential.PREFIX+'fast/fastunknot')
    with tarfile.open(fileobj=io.BytesIO(archive)) as handle:
        old = {member.name[len(differential.PREFIX):]:
               sha256(handle.extractfile(member).read()).hexdigest()
               for member in handle.getmembers() if member.isfile() and member.name.endswith('.py')}
    equal(historical['native_files_sha256'], old, 'historical complete native byte map')
    require(old.keys() == native.keys(), 'historical native file set')
    changed = sorted(name for name in native if native[name] != old[name])
    equal(changed, sorted(differential.CHANGED), 'only two native implementations changed')
    equal(historical['changed_native_files'], changed, 'recorded changed file set')
    equal(historical['unchanged_native_files'], 297, 'unchanged native module count')
    loaded = {}
    for basename in ('exact_lp', 'normal_euler_tree', 'normal_euler_transversal'):
        name = 'fast/fastunknot/'+basename+'.py'
        raw = differential.git('show', differential.REVISION+':'+differential.PREFIX+name)
        loaded[name] = sha256(raw).hexdigest()
        require(loaded[name] == old[name], 'git show/archive predecessor agreement')
    equal(historical['loaded_source_sha256'], loaded, 'actual archived-module source pins')


@contextmanager
def discovery_disabled():
    """Fail immediately if a saved-result checker reaches a producer solve."""
    from fastunknot import exact_lp, bounded_lp, source_kernel
    from fastunknot import normal_euler_tree, normal_euler_transversal
    targets = [(exact_lp, name) for name in (
        'solve_nonnegative_kernel', '_solve_prepared_nonnegative_kernel',
        '_prepare_kernel_matrix', '_solve_prepared_kernel', '_ellipsoid_kernel')]
    targets += [(bounded_lp, 'find_point'), (source_kernel.SourceKernel, 'extreme_witness'),
                (normal_euler_tree, 'search_euler_tree'),
                (normal_euler_tree._EulerMaskOracle, 'attempt'),
                (normal_euler_transversal, 'search_euler_transversal'),
                (normal_euler_tree, '_prepare_kernel_matrix'),
                (normal_euler_tree, '_solve_prepared_nonnegative_kernel')]
    saved = [(owner, name, getattr(owner, name)) for owner, name in targets]
    def forbidden(*args, **kwargs):
        raise RuntimeError('solver discovery is disabled during evidence replay')
    try:
        for owner, name, _ in saved:
            setattr(owner, name, forbidden)
        yield
    finally:
        for owner, name, original in reversed(saved):
            setattr(owner, name, original)


def restore_lp_numbers(value):
    """Undo json_safe only for raw LP results, whose numeric fields are ints.

    The source search certificates already use json_safe in their public
    schema, so this conversion is deliberately not applied to those results.
    """
    if type(value) is str and re.fullmatch(r'[+-]?0[xX][0-9a-fA-F]+', value):
        return int(value, 16)
    if type(value) is list:
        return [restore_lp_numbers(item) for item in value]
    if type(value) is dict:
        return {key: restore_lp_numbers(item) for key, item in value.items()}
    return value


def check_trace(checks):
    require(type(checks) is dict and set(checks) == {'count', 'events_rle', 'events_sha256'},
            'full raw callback trace fields')
    count = checks['count']
    require(type(count) is int and 0 <= count <= 10_000_000, 'bounded literal callback count')
    require(type(checks['events_rle']) is list, 'callback RLE list')
    events, previous = [], None
    for item in checks['events_rle']:
        require(type(item) is list and len(item) == 2, 'callback RLE pair')
        event, repetitions = item
        require(type(event) is list and len(event) in (2, 3) and
                all(type(v) in (str, int) for v in event), 'callback event signature')
        require(type(repetitions) is int and repetitions > 0, 'positive RLE multiplicity')
        require(event != previous and len(events)+repetitions <= count, 'canonical bounded RLE')
        events.extend([event]*repetitions)
        previous = event
    require(len(events) == count, 'callback RLE total')
    require(sha256(differential.dumps(events).encode()).hexdigest() == checks['events_sha256'],
            'callback event digest')
    return checks


def check_differential():
    path = DATA/'prepared-euler-matrix-differential.json'
    stdout = DATA/'prepared-euler-matrix-differential.txt'
    document = load(path)
    equal(document['schema'], 'prepared-euler-matrix-differential-v1', 'differential schema')
    equal(document['passed'], True, 'all differential cases passed')
    equal(document['seed'], differential.SEED, 'fixed differential seed')
    equal(document['source_pins_unchanged'], True, 'unchanged differential generation sources')
    native = differential.native_hashes()
    equal(document['native_files_sha256'], native, 'current differential native inputs')
    equal(document['native_files_after_sha256'], native, 'differential final native inputs')
    fixed = differential.fixed_hashes()
    equal(document['input_files_sha256'], fixed, 'runner/fixture source bytes')
    equal(document['input_files_after_sha256'], fixed, 'runner/fixture final bytes')
    closure = document['loaded_repository_module_sha256']
    check_pins(closure)
    expected = dict(native, **fixed)
    require(all(expected.get(name) == value for name, value in closure.items()),
            'loaded differential modules are within the pinned input closure')
    require(set(fixed) <= set(closure) and {'fast/fastunknot/'+name+'.py' for name in (
        'exact_lp', 'normal_euler_tree', 'normal_euler_transversal', 'normal_euler_tree_verify')}
        <= set(closure), 'required differential runtime modules')
    check_historical(document, native)
    lp_cases = differential.matrix_cases()
    fixtures, euler_cases = differential.euler_cases()
    equal(document['fixtures'], fixtures, 'literal regenerated layered fixtures')
    cases = [dict(case, kind='lp') for case in lp_cases] + euler_cases
    require(type(document['records']) is list and len(document['records']) == len(cases) == 492,
            'exact ordered differential coverage')
    statuses = Counter()
    with discovery_disabled():
        for record, case in zip(document['records'], cases):
            dynamic = {'historical', 'current', 'typed_output_equal', 'passed'}
            if case['kind'] == 'lp':
                dynamic.add('public_callback_trace_equal')
            equal({key: value for key, value in record.items() if key not in dynamic}, case,
                  'ordered declared input/options coverage')
            require(set(record) == set(case) | dynamic, 'exact differential record fields')
            equal(record['passed'], True, 'passed differential pair')
            equal(record['typed_output_equal'], True, 'typed equality flag')
            arms = [record['historical'], record['current']]
            for arm in arms:
                require(type(arm) is dict and set(arm) == {
                    'checks', 'replay', 'result', 'typed_result_sha256'}, 'successful retained arm')
            equal(arms[0]['result'], arms[1]['result'], 'literal retained both-arm output equality')
            outputs = [restore_lp_numbers(arm['result']) if case['kind'] == 'lp'
                       else arm['result'] for arm in arms]
            equal(outputs[0], outputs[1], 'restored type-sensitive output equality')
            for arm, result in zip(arms, outputs):
                require(arm['typed_result_sha256'] == sha256(differential.dumps(
                    differential.typed_form(result)).encode()).hexdigest(), 'typed original result digest')
            result = outputs[0]
            if case['kind'] == 'lp':
                equal(record['public_callback_trace_equal'], True, 'raw callback equality flag')
                traces = [check_trace(arm['checks']) for arm in arms]
                equal(traces[0], traces[1], 'normalized complete public callback order')
                replay = differential.replay_lp(case['matrix'], case['objective'], case['options'], result)
            else:
                for arm in arms:
                    require(type(arm['checks']) is dict and set(arm['checks']) == {'count'} and
                            type(arm['checks']['count']) is int and arm['checks']['count'] >= 0,
                            'source callback count; equality intentionally not required')
                replay = differential.replay_euler(fixtures[case['fixture']], case['allowed_types'], result)
            for arm in arms:
                equal(arm['replay'], replay, 'fresh independent replay equals saved arm summary')
            statuses[result['status']] += 1
    totals = dict(calls=984, failed_pairs=0, lp_pairs=348, pairs=492, passed_pairs=492,
                  raw_callback_trace_pairs=348, transversal_pairs=48, tree_pairs=96)
    equal(document['totals'], totals, 'differential totals')
    equal(document['statuses'], {arm: dict(statuses) for arm in ('historical', 'current')},
          'recomputed retained outcomes')
    scope = dict(benchmark=False, current_other_native_files_byte_equal=True,
        exhaustive_oracle=False, finite_differential=True, general_quasipolynomial=False,
        historical_sources_executed=True, negative_proofs_independently_replayed=True,
        original_primal_dual_and_positive_euler_replayed=True,
        raw_public_callback_order_compared=True, source_callbacks_may_change=True, timings_recorded=False)
    equal(document['scope'], scope, 'finite untimed differential scope')
    log = load(stdout)
    for key in ('schema', 'passed', 'totals', 'statuses', 'source_pins_unchanged'):
        equal(log[key], document[key], 'differential stdout binding')
    equal(log['native_files'], 299, 'logged native file count')
    equal(log['historical_revision'], differential.REVISION, 'logged predecessor revision')
    equal(log['timings_recorded'], False, 'no differential timings')
    equal(log['general_quasipolynomial'], False, 'no differential global bound')
    require(log['output_sha256'] == digest(path) and Path(log['output']).name == path.name,
            'differential stdout artifact digest')
    return dict(totals=totals, statuses=dict(statuses), discovery_disabled=True,
                fresh_saved_result_replay=True, native_files=299,
                historical_revision=differential.REVISION), {path, stdout, DATA/'prepared_euler_matrix_differential.py'}


def check_pilot():
    """Bind the separately executed, discovery-disabled pilot replay."""
    archive = DATA/'lp-pivot-pilot-973c6fdee.tar.gz'
    helper = DATA/'lp_pivot_pilot_replay.py'
    record_path = DATA/'lp-pivot-pilot-replay.json'
    stdout_path = DATA/'lp-pivot-pilot-replay.txt'
    import lp_pivot_pilot_replay as pilot
    record = load(record_path)
    equal(record['schema'], 'lp-pivot-pilot-archive-replay-v1', 'pilot replay schema')
    equal(record['passed'], True, 'pilot replay passed')
    equal(record['phase'], 'complete', 'complete pilot replay')
    equal(record['failures'], [], 'no pilot replay failures')
    equal(record['coverage'], dict(control_queries=21, callback_arms=3,
          captured_queries=8, fixed_comparison_records=24), 'exact pilot replay coverage')
    equal(record['returned_summary'], pilot.EXPECTED_RETURNED, 'exact pilot outcomes/work')
    equal(record['snapshot_revision'], differential.REVISION, 'pilot archived predecessor')
    equal(record['snapshot_manifest_sha256'], pilot.SNAPSHOT_MANIFEST_SHA256,
          'pilot frozen source manifest')
    equal(record['member_count'], 317, 'pilot member count')
    equal(record['member_bytes'], 10673636, 'pilot uncompressed bytes')
    equal(record['archive']['bytes'], 1063563, 'pilot compressed bytes')
    require(record['archive']['sha256'] == digest(archive) ==
            'c894a7b69a3127ffba539290fabae1f95a6a5e0e297d1134aa99a9b743222867',
            'frozen pilot archive digest')
    require(Path(record['archive']['path']).name == archive.name, 'pilot archive path binding')
    require(record['replay_helper_sha256'] == digest(helper), 'executed pilot replay helper bytes')
    payloads = pilot.checked_members(archive)  # Hash validation only; no extraction or subprocess.
    equal(record['archive_members'], {name: dict(bytes=len(raw), sha256=sha256(raw).hexdigest())
          for name, raw in sorted(payloads.items())}, 'every pilot archive member')
    equal(record['subprocess']['returncode'], 0, 'literal successful pilot return code')
    require(record['subprocess']['stdout_sha256'] == digest(stdout_path), 'pilot stdout bytes')
    require(record['subprocess']['stderr_sha256'] == sha256(b'').hexdigest(), 'empty pilot stderr')
    equal(load(stdout_path), record['returned_summary'], 'pilot replay log/result binding')
    command = record['command']
    require(type(command) is list and len(command) == 11 and
            all(type(item) is str for item in command), 'literal isolated replay command')
    equal(command[1:3], ['-B', '-S'], 'isolated Python flags')
    equal(command[4:6], ['check', '--controls'], 'replay command, not discovery')
    equal(command[7], '--capture', 'capture input argument')
    equal(command[9], '--comparison', 'comparison input argument')
    pilot_root = Path(command[3]).parent
    require(pilot_root.name == 'lp-pivot-pilot' and Path(command[3]).name == 'pilot.py',
            'archived pilot entry point')
    for index, name in ((6, 'controls'), (8, 'capture'), (10, 'comparison')):
        require(Path(command[index]) == pilot_root/'results'/(name+'.json'),
                'exact isolated archived input paths')
    flags = dict(discovery_disabled=True, current_native_imported=False,
        archived_native_snapshot_only=True, timings_claimed=False,
        whole_call_shared_budget_claimed=False, general_quasipolynomial_claimed=False)
    equal({key: record[key] for key in flags}, flags, 'pilot provenance and claim scope')
    return dict(coverage=record['coverage'], returned_summary=record['returned_summary'],
                archive_sha256=digest(archive), member_count=317,
                retained_discovery_disabled_replay=True, replay_subprocess_run_here=False,
                timings_claimed=False, whole_call_shared_budget_claimed=False), \
        {archive, helper, record_path, stdout_path}


def check_builds(core_manifest):
    baseline = DATA/'prepared-euler-matrix-latex-3.txt'
    require(digest(baseline) == core_manifest['files_sha256'][str(baseline.relative_to(ROOT))],
            'authenticated core diagnostic baseline')
    builds = [DATA/f'{PREFIX}-latex-{i}.txt' for i in (1, 2, 3)]
    for path in builds:
        contents = path.read_text()
        require('Output written on report.pdf' in contents, 'completed evidence PDF build')
        require(not re.search(r'^!|Emergency stop|Fatal error occurred', contents, re.M),
                'no fatal TeX diagnostic')
    final = builds[-1].read_text()
    require(not re.search(r'undefined references|undefined on input|Rerun to get|'
                          r'Label\(s\) may have changed|multiply.defined labels', final),
            'settled references and labels')
    require(not (core.diagnostics(final)-core.diagnostics(baseline.read_text())),
            'no new warnings or box diagnostics relative to core')
    matches = re.findall(r'Output written on report\.pdf \((\d+) pages, (\d+) bytes\)', final)
    require(len(matches) == 1, 'one final PDF completion line')
    pages, size = map(int, matches[0])
    pdf = ROOT/'synthesis/report.pdf'
    require(pdf.read_bytes().startswith(b'%PDF-') and pdf.stat().st_size == size,
            'current PDF byte size matches final build')
    tex = included_tex(ROOT/'synthesis/report.tex')
    require({ROOT/'synthesis/prepared_euler_matrix.tex',
             ROOT/'synthesis/q_zero_pachner_transport.tex',
             ROOT/'synthesis/capped_pivot_pilot.tex'} <= tex, 'new article inclusion')
    return dict(report_pages=pages, report_bytes=size, included_tex_files=len(tex)), \
        tex | set(builds) | {pdf, baseline, ROOT/'fast/README.md', ROOT/'synthesis/README.md'}


def main():
    if not __debug__:
        raise RuntimeError('evidence verification requires assertions enabled')
    manifest, tested, files = check_core()
    preflight, more = check_preflight()
    files |= more
    differential_summary, more = check_differential()
    files |= more
    pilot, more = check_pilot()
    files |= more
    builds, more = check_builds(manifest)
    files |= more
    files |= {ROOT/name for name in tested} | {Path(__file__).resolve(),
        DATA/'strict_pachner32_publication.py',
        ROOT/'fast/strict_pachner32_research/common.py',
        ROOT/'fast/strict_pachner32_research/check_evidence.py'}
    files = python_dependencies(files)
    require(all(path.is_file() and path.is_relative_to(ROOT) for path in files), 'complete publication closure')
    equal(core.test_source_files(), tested, 'tested sources unchanged during replay')
    result = dict(schema='prepared-euler-evidence-publication-v1', passed=True,
        tests=394, test_modules=44, skipped_tests=0, tested_files=len(tested),
        core_commit=CORE_COMMIT, core_manifest_sha256=CORE_MANIFEST_SHA256,
        differential=differential_summary, pilot=pilot, preflight=preflight, **builds,
        general_quasipolynomial=False, new_timing_claims=False,
        tests_or_build_run_by_this_helper=False, solver_discovery_run_by_this_helper=False,
        certificate_replay_run_by_this_helper=True,
        files_sha256={str(path.relative_to(ROOT)): digest(path) for path in sorted(files)})
    (DATA/f'{PREFIX}-publication.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'files_sha256'}, sort_keys=True))


if __name__ == '__main__':
    main()
