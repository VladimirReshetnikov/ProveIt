"""Replay and pin the complete strict-Pachner-3--2 evidence publication.

This helper runs no discovery, benchmarks, historical publication checkers,
or PDF builds. Run after the final three-pass PDF and retained replay logs.
"""
import argparse
import ast
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
sys.path.insert(0, str(ROOT/'fast'))
from strict_pachner32_research.common import ARMS, source_hashes
from strict_pachner32_research.check_evidence import check_benchmark


def file_digest(path):
    return sha256(path.read_bytes()).hexdigest()


def recorded_summary(path):
    lines = [line for line in path.read_text().splitlines() if line.strip()]
    assert lines, 'empty replay log: '+str(path)
    result = json.loads(lines[-1])
    assert type(result) is dict and result.get('passed') is True
    return result


def python_dependencies(paths):
    """Find the local static-import closure, including package initializers."""
    fast = ROOT/'fast'
    found, visited = set(paths), set()
    pending = [p for p in paths if p.suffix == '.py' and p.is_relative_to(fast)]

    def add_module(name):
        parts = name.split('.') if name else []
        for end in range(1, len(parts)+1):
            stem = fast.joinpath(*parts[:end])
            choices = [stem/'__init__.py']
            if end == len(parts):
                choices.append(stem.with_suffix('.py'))
            for path in choices:
                if path.is_file() and path not in found:
                    found.add(path)
                    pending.append(path)

    while pending:
        path = pending.pop()
        if path in visited:
            continue
        visited.add(path)
        package = list(path.relative_to(fast).with_suffix('').parts[:-1])
        for node in ast.walk(ast.parse(path.read_text(), filename=str(path))):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    add_module(alias.name)
            elif isinstance(node, ast.ImportFrom):
                assert node.level <= len(package)+1
                prefix = package[:len(package)-node.level+1] if node.level else []
                name = '.'.join(prefix+([node.module] if node.module else []))
                add_module(name)
                for alias in node.names:
                    if alias.name != '*':
                        add_module('.'.join(part for part in (name, alias.name) if part))
    return found


def included_tex(start):
    """Pin literal input/include dependencies of the complete report."""
    synthesis = ROOT/'synthesis'
    pending, found = [start.resolve()], set()
    while pending:
        path = pending.pop()
        if path in found:
            continue
        assert path.is_file() and path.is_relative_to(ROOT), 'missing TeX source: '+str(path)
        found.add(path)
        # All maintained report includes use literal braced paths. Ignore
        # ordinary TeX comments before finding those dependency declarations.
        contents = re.sub(r'(?<!\\)%[^\n]*', '', path.read_text())
        for name in re.findall(r'\\(?:input|include)\s*\{([^{}]+)\}', contents):
            assert '\\' not in name and '#' not in name, 'dynamic TeX include: '+name
            relative = Path(name)
            if not relative.suffix:
                relative = relative.with_suffix('.tex')
            # pdflatex runs with synthesis as cwd, including nested inputs.
            child = (synthesis/relative).resolve()
            if not child.is_file():
                child = (path.parent/relative).resolve()
            pending.append(child)
    return found


def main():
    if not __debug__:
        raise RuntimeError('publication replay requires Python assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', type=Path, default=DATA/'strict-pachner32-audit.json')
    parser.add_argument('--benchmark', type=Path, default=DATA/'strict-pachner32-benchmark.json')
    parser.add_argument('--environment', type=Path, default=DATA/'strict-pachner32-environment.json')
    parser.add_argument('--replay-log', type=Path, default=DATA/'strict-pachner32-replay.txt')
    parser.add_argument('--timing-replay-log', type=Path, default=DATA/'strict-pachner32-timing-replay.txt')
    parser.add_argument('--output', type=Path, default=DATA/'strict-pachner32-publication.json')
    args = parser.parse_args()

    pins = source_hashes()
    raw = args.audit.read_bytes()
    audit = json.loads(raw)
    benchmark = json.loads(args.benchmark.read_bytes())
    # Includes fresh independent audit replay, all archived source/move/negative
    # proofs and manifest hashes. Historical native pins remain historical.
    assert check_benchmark(benchmark, audit, raw)
    assert audit['coverage'] == dict(ordinary_calls_expected=8, ordinary_calls_completed=8)
    assert len(audit['records']) == 4 and len(benchmark['records']) == 3
    assert benchmark['calls_completed'] == 30
    outcomes = {arm: [r['arms'][arm]['result']['status'] for r in audit['records']] for arm in ARMS}
    archived = audit['archival_replay']
    assert archived['initial_diagram_chains'] == 3 and archived['legacy_moves'] == 9
    assert archived['full_root_negative_queries'] == 3
    assert archived['selfattached_region_pairs'] == 2
    assert archived['malformed_controls_rejected'] == 29
    assert [r['tetrahedron_trace'][-1] for r in archived['records']] == [8, 12, 17]
    assert [r['h_upper_bound'] for r in archived['records']] == [1, 1, 3]
    assert all(r['full_root_negative_verified'] is True for r in archived['records'])
    replay_log = recorded_summary(args.replay_log)
    timing_log = recorded_summary(args.timing_replay_log)
    expected_summary = dict(passed=True, ordinary_calls=8, discovery_used=False,
        general_quasipolynomial=False, source_files=len(pins),
        archival_initial_chains=3, archival_moves=9, archival_negative_queries=3,
        outcomes=outcomes)
    assert replay_log == expected_summary
    eligible = [r['id'] for r in benchmark['records'] if r['summary']['eligible_common_complete_outcome']]
    assert timing_log == dict(expected_summary, benchmark_cases=3,
        timed_and_warmup_calls=30, eligible_cases=eligible)
    environment = json.loads(args.environment.read_bytes())
    assert type(environment) is dict and environment, 'missing benchmark environment record'

    tests = DATA/'strict-pachner32-tests.txt'
    test_log = tests.read_text()
    assert re.search(r'Ran 267 tests in [0-9.]+s\s+OK\s*$', test_log)
    assert not re.search(r'\b(?:FAILED|ERROR|skipped)\b', test_log, re.IGNORECASE)
    command = DATA/'strict-pachner32-test-command.txt'
    modules = set(re.findall(r'\btests\.(test_[A-Za-z0-9_]+)\b', command.read_text()))
    assert len(modules) == 29
    assert {'test_normal_pachner32', 'test_normal_pachner32_verify',
            'test_pachner32_crushing', 'test_pachner32',
            'test_factored_crushing', 'test_factored_crushing_verify'} <= modules
    test_files = {ROOT/'fast/tests'/(name+'.py') for name in modules}
    assert all(path.is_file() for path in test_files)

    controls = DATA/'strict-pachner32-corruption-controls.json'
    control_script = DATA/'strict-pachner32-corruption-controls.py'
    control_fixture = DATA/'strict-pachner32-corruption-fixture.json'
    corruption = json.loads(controls.read_bytes())
    assert corruption['passed'] is True and corruption['valid_control'] is True
    rejected = corruption['rejected_mutations']
    assert type(rejected) is int and rejected == 27
    assert corruption['source_sha256'] == pins
    assert corruption['script_sha256'] == file_digest(control_script)
    assert corruption['fixture_sha256'] == file_digest(control_fixture)
    assert len(corruption['records']) == rejected
    assert len({r['name'] for r in corruption['records']}) == rejected
    assert all(r['rejected'] is True for r in corruption['records'])

    # Earlier core build logs are retained and hashed as historical artifacts;
    # only these final three passes attest the complete evidence publication.
    build_logs = [DATA/f'strict-pachner32-latex-{i}.txt' for i in (1, 2, 3)]
    for path in build_logs:
        assert 'Output written on report.pdf' in path.read_text(), 'failed final PDF pass: '+path.name
    last_build = build_logs[-1].read_text()
    assert not re.search(r'undefined references|undefined on input|Rerun to get|Label\(s\) may have changed|multiply.defined labels', last_build)
    match = re.search(r'Output written on report\.pdf \((\d+) pages, (\d+) bytes\)', last_build)
    assert match, 'missing final PDF page/byte count'
    pdf = ROOT/'synthesis/report.pdf'
    pdf_bytes = pdf.read_bytes()
    assert pdf_bytes.startswith(b'%PDF-') and len(pdf_bytes) == int(match[2])
    includes = ROOT/'synthesis/marked_cut_handlebodies.tex'
    assert r'\input{strict_pachner32.tex}' in includes.read_text()
    report_tex = ROOT/'synthesis/report.tex'
    tex = included_tex(report_tex)
    assert ROOT/'synthesis/strict_pachner32.tex' in tex

    required = {args.audit.resolve(), args.benchmark.resolve(), args.environment.resolve(),
        args.replay_log.resolve(), args.timing_replay_log.resolve(), tests, command, *build_logs,
        controls, control_script, control_fixture, pdf, includes, report_tex, Path(__file__).resolve(),
        ROOT/'synthesis/strict_pachner32.tex', ROOT/'synthesis/README.md', ROOT/'fast/README.md'}
    # Explicit data dependencies of the new source regression and its legacy
    # Pachner controls. Their embedded historical pins are not reinterpreted.
    required.update({DATA/'boundary-unlayer-audit.json',
        ROOT/'fast/conflict_composition_research/data/generation/tt-state.json.gz',
        DATA/'coherent-obstruction-certificate.json'})
    for name in ('strict-pachner32-audit.txt', 'strict-pachner32-benchmark.txt'):
        path = DATA/name
        assert path.read_text().rstrip().endswith('PASSED'), 'unfinished discovery/timing log: '+name
        required.add(path)
    assert all(path.is_file() for path in required)
    files = python_dependencies({ROOT/name for name in pins} | test_files | required | tex)
    files.update(path for path in DATA.glob('strict-pachner32-*') if path.is_file())
    files.discard(args.output.resolve())
    files.discard(DATA/'strict-pachner32-publication.json')
    files.discard(DATA/'strict-pachner32-publication.txt')
    assert all(path.is_relative_to(ROOT) for path in files)
    assert source_hashes() == pins, 'source changed during publication replay'
    manifest = dict(schema='strict-pachner32-publication-v1', passed=True,
        general_quasipolynomial=False,
        strict_preprocessing_polynomial=True,
        resolving_parameter_monotonicity_claimed=False,
        measured_scope='Whole-diagram native crushing, baseline versus optional strict Pachner 3--2 preprocessing, under identical shared finite work allowances; every returned proof or partial chain independently replayed.',
        counter_scope='Recorded nonnegative counter bounds and exact mixed-chain reduction counts; no independent replay of the discovery LP operation trace.',
        historical_scope='Archived generation and old native pin maps remain historical; current checks replay the supplied three initial chains, nine local moves, three full-root negative Euler proofs and selfattachment control.',
        resolving_bounds_scope='Upper bounds derived only from the exact archived terminal source trees; no assertion about all homeomorphic triangulations, exact h values, or a general family bound.',
        source_pins_verified=True, discovery_run_by_this_helper=False,
        audit=dict(ordinary_cases=4, ordinary_calls=8,
                   outcomes={arm: dict(Counter(statuses)) for arm, statuses in outcomes.items()}),
        archived_replay=audit['archival_replay'],
        benchmark=dict(cases=3, timed_and_warmup_calls=30, eligible_cases=eligible,
            inconclusive_calls=sum(r['warmups'][arm]['status'] == 'INCONCLUSIVE'
                for r in benchmark['records'] for arm in ARMS)+
                sum(p['samples'][arm]['status'] == 'INCONCLUSIVE' for r in benchmark['records']
                    for p in r['paired'] for arm in ARMS)+
                sum(s['status'] == 'INCONCLUSIVE' for r in benchmark['records'] for s in r['aa']['samples'])),
        tests=267, test_modules=29, skipped_tests=0, rejected_corruption_controls=rejected,
        report_pages=int(match[1]), report_bytes=len(pdf_bytes), included_tex_files=len(tex),
        replayed_source_sha256=pins,
        files_sha256={str(path.relative_to(ROOT)): file_digest(path) for path in sorted(files)})
    assert source_hashes() == pins, 'source changed while hashing publication'
    args.output.write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps(dict(passed=True, ordinary_calls=8, benchmark_calls=30,
        tests=267, rejected_corruption_controls=rejected,
        general_quasipolynomial=False, pinned_files=len(files)), sort_keys=True))


if __name__ == '__main__':
    main()
