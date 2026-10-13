"""Replay and pin the complete fixed-total-one-upward evidence publication.

Run after the final PDF, independent replay logs and controls exist. No search,
benchmark, tests, PDF builds, or historical publication main() is run here.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
sys.path.insert(0, str(ROOT/'fast'))
from pachner_descent_research.common import ARMS, BENCHMARK_PROTOCOL, source_hashes
from pachner_descent_research.check_evidence import check_benchmark
from pachner_descent_endpoint_binding import check_endpoint_bindings
# Import deterministic dependency walkers only; old main() is never invoked.
from strict_pachner32_publication import included_tex, python_dependencies


def file_digest(path):
    return sha256(path.read_bytes()).hexdigest()


def same(actual, expected):
    if type(actual) is not type(expected):
        return False
    if type(expected) is dict:
        return actual.keys() == expected.keys() and all(same(actual[k], v) for k, v in expected.items())
    if type(expected) in (tuple, list):
        return len(actual) == len(expected) and all(same(a, b) for a, b in zip(actual, expected))
    return actual == expected


def recorded_summary(path):
    lines = [line for line in path.read_text().splitlines() if line.strip()]
    assert lines, 'empty replay log: '+str(path)
    result = json.loads(lines[-1])
    assert type(result) is dict and result.get('passed') is True
    return result


def main():
    if not __debug__:
        raise RuntimeError('publication replay requires assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', type=Path, default=DATA/'pachner-descent-audit.json')
    parser.add_argument('--benchmark', type=Path, default=DATA/'pachner-descent-benchmark.json')
    parser.add_argument('--environment', type=Path, default=DATA/'pachner-descent-environment.json')
    parser.add_argument('--replay-log', type=Path, default=DATA/'pachner-descent-replay.txt')
    parser.add_argument('--timing-replay-log', type=Path, default=DATA/'pachner-descent-timing-replay.txt')
    parser.add_argument('--endpoint-bindings', type=Path, default=DATA/'pachner-descent-endpoint-bindings.json')
    parser.add_argument('--output', type=Path, default=DATA/'pachner-descent-publication.json')
    args = parser.parse_args()
    pins = source_hashes()
    audit_raw = args.audit.read_bytes()
    audit = json.loads(audit_raw)
    benchmark = json.loads(args.benchmark.read_bytes())
    # Includes fresh whole/partial proof replay and both immutable historical
    # archive groups, with exact STANDARD ranks and source-specific h bounds.
    assert check_benchmark(benchmark, audit, audit_raw)
    assert same(audit['coverage'], dict(ordinary_calls_expected=14, ordinary_calls_completed=14))
    assert len(audit['records']) == 7 and len(benchmark['records']) == 5
    assert same(benchmark['calls_completed'], 50)
    outcomes = {arm: [r['arms'][arm]['result']['status'] for r in audit['records']] for arm in ARMS}
    archived = audit['archival_replay']
    old, staged = archived['earlier_stages'], archived['fixed_u1_stages']
    assert old['preprocessing_calls'] == old['supplied_source_queries'] == old['local_descent_calls'] == 3
    assert old['original_standard_rays'] == 11
    assert staged['calls'] == 20 and staged['whole_circle_calls'] == 2
    assert staged['preprocessing_calls'] == 12 and staged['supplied_source_queries'] == 6
    assert staged['assembled_negative_proofs'] == 5 and staged['original_standard_rays'] == 10
    assert staged['accepted_preprocessing_macros'] == 13
    assert [r['exact_h'] for r in staged['records']] == [1, 0, 2, 1, 2, None]
    assert [r['tetrahedra'] for r in staged['records']] == [7, 10, 16, 11, 17, 31]
    prior = archived['strict32_prerequisite']
    assert prior['initial_diagram_chains'] == 3 and prior['legacy_moves'] == 9
    assert prior['full_root_negative_queries'] == 3
    assert prior['selfattached_region_pairs'] == 2 and prior['malformed_controls_rejected'] == 29

    # The frozen package checks archive-to-archive equalities. This independent
    # external helper additionally binds all twelve fresh endpoints to those
    # exact staged sources; no h-transport under homeomorphism is assumed.
    endpoint_script = DATA/'pachner_descent_endpoint_binding.py'
    endpoints = check_endpoint_bindings(audit)
    expected_endpoints = dict(endpoints, audit_sha256=sha256(audit_raw).hexdigest(),
                             script_sha256=file_digest(endpoint_script))
    assert same(json.loads(args.endpoint_bindings.read_bytes()), expected_endpoints)
    assert endpoints['endpoint_bindings'] == 12

    expected_summary = dict(passed=True, ordinary_calls=14, discovery_used=False,
        general_quasipolynomial=False, source_files=len(pins),
        archival_old_preprocessing_calls=3, archival_old_source_queries=3,
        archival_local_descents=3, archival_staged_calls=20,
        archival_staged_assembled_proofs=5, archival_standard_rays=21,
        outcomes=outcomes)
    assert same(recorded_summary(args.replay_log), expected_summary)
    eligible = [r['id'] for r in benchmark['records'] if r['summary']['eligible_common_complete_outcome']]
    assert same(eligible, BENCHMARK_PROTOCOL['case_ids']), 'not all five planned cases have common completed outcomes'
    assert same(recorded_summary(args.timing_replay_log), dict(expected_summary,
        benchmark_cases=5, timed_and_warmup_calls=50, eligible_cases=eligible))
    environment = json.loads(args.environment.read_bytes())
    assert type(environment) is dict and environment
    assert type(environment.get('returncode')) is int and environment['returncode'] == 0
    assert same(environment.get('affinity'), [5])
    executed = environment.get('command')
    assert type(executed) is list and len(executed) == 9
    assert all(type(part) is str and part for part in executed)
    assert executed[1:6] == ['-B', '-S', '-m', 'pachner_descent_research.benchmark', '--audit']
    assert executed[7] == '--output'
    assert (ROOT/'fast'/executed[6]).resolve() == args.audit.resolve()
    assert (ROOT/'fast'/executed[8]).resolve() == args.benchmark.resolve()
    assert environment.get('python') == benchmark['python']
    assert environment.get('platform') == benchmark['platform']
    assert type(environment.get('before')) is dict and type(environment.get('after')) is dict

    command = DATA/'pachner-descent-test-command.txt'
    modules = set(re.findall(r'\btests\.(test_[A-Za-z0-9_]+)\b', command.read_text()))
    assert len(modules) == 38
    assert {'test_normal_pachner_descent', 'test_normal_pachner_descent_verify',
            'test_pachner_descent_crushing', 'test_pachner_cover_search',
            'test_pachner_cover_oracle', 'test_factored_crushing'} <= modules
    test_files = {ROOT/'fast/tests'/(name+'.py') for name in modules}
    test_logs = [(DATA/'pachner-descent-tests.txt', 336),
                 (DATA/'pachner-descent-integration-tests.txt', 18),
                 (DATA/'pachner-descent-verifier-final-tests.txt', 7)]
    for path, count in test_logs:
        contents = path.read_text()
        assert re.search(r'Ran '+str(count)+r' tests in [0-9.]+s\s+OK\s*$', contents)
        assert not re.search(r'\b(?:FAILED|ERROR|skipped)\b', contents, re.I)

    controls = DATA/'pachner-descent-corruption-controls.json'
    control_script = DATA/'pachner-descent-corruption-controls.py'
    control_fixture = DATA/'pachner-descent-corruption-fixture.json'
    corruption = json.loads(controls.read_bytes())
    assert corruption['passed'] is True and corruption['valid_control'] is True
    rejected = corruption['rejected_mutations']
    assert type(rejected) is int and rejected == 49
    assert same(corruption['source_sha256'], pins)
    assert corruption['script_sha256'] == file_digest(control_script)
    assert corruption['fixture_sha256'] == file_digest(control_fixture)
    assert corruption['audit_sha256'] == sha256(audit_raw).hexdigest()
    assert corruption['endpoint_helper_sha256'] == file_digest(endpoint_script)
    assert corruption['native_valid_alternate_endpoint'] is True
    assert same(corruption['endpoint_bindings'], 12)
    fixture = json.loads(control_fixture.read_bytes())
    assert fixture['schema'] == 'pachner-descent-corruption-fixture-v1'
    assert same(fixture['source_sha256'], pins)
    assert fixture['audit_sha256'] == sha256(audit_raw).hexdigest()
    fixture_audit = Path(fixture['audit_file'])
    assert not fixture_audit.is_absolute() and fixture_audit.name == str(fixture_audit)
    assert (DATA/fixture_audit).resolve() == args.audit.resolve()
    assert len(corruption['records']) == rejected
    assert len({r['name'] for r in corruption['records']}) == rejected
    assert all(r['rejected'] is True for r in corruption['records'])

    # The old core manifest and logs remain immutable historical artifacts.
    # Only these three new logs attest the final evidence-inclusive PDF.
    build_logs = [DATA/f'pachner-descent-latex-{i}.txt' for i in (1, 2, 3)]
    for path in build_logs:
        assert 'Output written on report.pdf' in path.read_text(), 'failed final PDF pass: '+path.name
    final = build_logs[-1].read_text()
    assert not re.search(r'undefined references|undefined on input|Rerun to get|Label\(s\) may have changed|multiply.defined labels', final)
    match = re.search(r'Output written on report\.pdf \((\d+) pages, (\d+) bytes\)', final)
    assert match
    pdf = ROOT/'synthesis/report.pdf'
    pdf_bytes = pdf.read_bytes()
    assert pdf_bytes.startswith(b'%PDF-') and len(pdf_bytes) == int(match[2])
    report_tex = ROOT/'synthesis/report.tex'
    includes = ROOT/'synthesis/marked_cut_handlebodies.tex'
    tex = included_tex(report_tex)
    assert len(tex) == 546 and ROOT/'synthesis/pachner_descent_crushing.tex' in tex
    assert r'\input{pachner_descent_crushing.tex}' in includes.read_text()

    required = {args.audit.resolve(), args.benchmark.resolve(), args.environment.resolve(),
        args.replay_log.resolve(), args.timing_replay_log.resolve(), args.endpoint_bindings.resolve(),
        endpoint_script, command, *[path for path, _ in test_logs], *build_logs,
        controls, control_script, control_fixture, pdf, includes, report_tex,
        Path(__file__).resolve(), DATA/'strict_pachner32_publication.py',
        DATA/'pachner_descent_core_publication.py', DATA/'pachner-descent-core-publication.json',
        DATA/'pachner_descent_benchmark_run.py', ROOT/'synthesis/pachner_descent_crushing.tex',
        ROOT/'synthesis/README.md', ROOT/'fast/README.md'}
    # All explicit serialized test fixtures from the core publication,
    # including three dynamic reads that static Python imports cannot find.
    serialized_fixtures = {DATA/'boundary-unlayer-audit.json', DATA/'coherent-obstruction-certificate.json',
        ROOT/'reports/79/repro/fast/commitment_research/coherent-obstruction-certificate.json',
        ROOT/'reports/79/repro/fast/shared_cover_research/results/exhaustion.json',
        ROOT/'fast/tests/fixtures/causal_noncanonical.json',
        ROOT/'fast/conflict_composition_research/data/generation/tt-state.json.gz',
        ROOT/'fast/strict_pachner32_research/data/generation/euler-queries.json.gz'}
    required.update(serialized_fixtures)
    # Reusing retained test logs is justified by exact bytes of all tested
    # native code, static test dependencies, and explicit dynamic fixtures.
    # Changed report prose and the new research package are outside this set.
    core = json.loads((DATA/'pachner-descent-core-publication.json').read_bytes())
    assert core['schema'] == 'pachner-descent-core-publication-v1' and core['passed'] is True
    assert core['tests'] == 336 and core['test_modules'] == 38
    tested_files = python_dependencies(set((ROOT/'fast/fastunknot').rglob('*.py')) |
                                      test_files | serialized_fixtures)
    tested_files.update((command, *[path for path, _ in test_logs]))
    for path in tested_files:
        relative = str(path.relative_to(ROOT))
        assert relative in core['files_sha256'], 'test dependency missing from core pins: '+relative
        assert file_digest(path) == core['files_sha256'][relative], 'retained tests stale for: '+relative
    # The audit was launched without stdout redirection. Its complete raw JSON
    # is mandatory; no nonexistent audit text log is invented or required.
    benchmark_log = DATA/'pachner-descent-benchmark.txt'
    assert benchmark_log.read_text().rstrip().endswith('PASSED')
    required.add(benchmark_log)
    assert all(path.is_file() for path in required)
    files = python_dependencies({ROOT/name for name in pins} | test_files | required | tex)
    files.update(path for path in DATA.glob('pachner-descent-*') if path.is_file())
    files.discard(args.output.resolve())
    files.discard(DATA/'pachner-descent-publication.json')
    files.discard(DATA/'pachner-descent-publication.txt')
    assert all(path.is_file() and path.is_relative_to(ROOT) for path in files)
    assert source_hashes() == pins, 'source changed during publication replay'
    manifest = dict(schema='pachner-descent-publication-v1', passed=True,
        general_quasipolynomial=False, fixed_one_upward_preprocessing_polynomial=True,
        resolving_parameter_monotonicity_claimed=False,
        measured_scope='Fourteen fresh whole-diagram calls and fifty predeclared benchmark calls, baseline versus optional fixed-total-one-upward strict preprocessing, with strict32 enabled and identical other controls.',
        counter_scope='Recorded nonnegative bounds and exact mixed-chain operation counts; no independent replay of discovery LP/search operation traces.',
        historical_scope='Core publication and archived generation/native pins remain historical. Current validators replay both retained archive groups and strict32 prerequisites without invoking historical publication main routines.',
        resolving_bounds_scope='Source-specific STANDARD-rank lower bounds and negative-tree upper bounds; all twelve fresh endpoints equal their staged sources exactly. No h-transport between distinct triangulations or family bound is claimed.',
        source_pins_verified=True, discovery_run_by_this_helper=False,
        audit=dict(ordinary_cases=7, ordinary_calls=14,
            outcomes={arm: dict(Counter(statuses)) for arm, statuses in outcomes.items()}),
        archived_replay=archived, endpoint_bindings=endpoints,
        benchmark=dict(cases=5, timed_and_warmup_calls=50, eligible_cases=eligible,
            inconclusive_calls=sum(r['warmups'][arm]['status'] == 'INCONCLUSIVE'
                for r in benchmark['records'] for arm in ARMS)+
                sum(p['samples'][arm]['status'] == 'INCONCLUSIVE' for r in benchmark['records']
                    for p in r['paired'] for arm in ARMS)+
                sum(s['status'] == 'INCONCLUSIVE' for r in benchmark['records'] for s in r['aa']['samples'])),
        tests=336, test_modules=38, focused_integration_tests=18,
        final_focused_verifier_tests=7, skipped_tests=0, rejected_corruption_controls=rejected,
        tested_dependency_bytes_unchanged=True, tested_files_bound_to_core=len(tested_files),
        report_pages=int(match[1]), report_bytes=len(pdf_bytes), included_tex_files=len(tex),
        replayed_source_sha256=pins,
        files_sha256={str(path.relative_to(ROOT)): file_digest(path) for path in sorted(files)})
    assert source_hashes() == pins, 'source changed while hashing publication'
    args.output.write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps(dict(passed=True, ordinary_calls=14, benchmark_calls=50,
        endpoint_bindings=12, tests=336, final_focused_verifier_tests=7,
        rejected_corruption_controls=rejected, general_quasipolynomial=False,
        pinned_files=len(files)), sort_keys=True))


if __name__ == '__main__':
    main()
