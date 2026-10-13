"""Replay and pin the complete factored-crushing evidence publication.

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
from factored_crushing_research.common import ARMS, source_hashes
from factored_crushing_research.check_evidence import check_benchmark


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
    parser.add_argument('--audit', type=Path, default=DATA/'factored-crushing-audit.json')
    parser.add_argument('--benchmark', type=Path, default=DATA/'factored-crushing-benchmark.json')
    parser.add_argument('--environment', type=Path, default=DATA/'factored-crushing-environment.json')
    parser.add_argument('--replay-log', type=Path, default=DATA/'factored-crushing-replay.txt')
    parser.add_argument('--timing-replay-log', type=Path, default=DATA/'factored-crushing-timing-replay.txt')
    parser.add_argument('--output', type=Path, default=DATA/'factored-crushing-publication.json')
    args = parser.parse_args()

    pins = source_hashes()
    raw = args.audit.read_bytes()
    audit = json.loads(raw)
    benchmark = json.loads(args.benchmark.read_bytes())
    # check_benchmark includes complete, independent check_audit replay.
    assert check_benchmark(benchmark, audit, raw)
    assert audit['scaling_requested'] is True and len(audit['scaling']) == 4
    assert audit['coverage'] == dict(ordinary_calls_expected=16, ordinary_calls_completed=16,
                                   scaling_calls_expected=4, scaling_calls_completed=4)
    assert len(audit['records']) == 8 and len(benchmark['records']) == 5
    assert benchmark['calls_completed'] == 50
    outcomes = {arm: [r['arms'][arm]['result']['status'] for r in audit['records']] for arm in ARMS}
    expected_summary = dict(passed=True, ordinary_calls=16, scaling_calls=4,
        general_quasipolynomial=False, discovery_used=False, outcomes=outcomes,
        source_files=len(pins))
    assert recorded_summary(args.replay_log) == expected_summary
    eligible = [r['id'] for r in benchmark['records'] if r['summary']['eligible_common_complete_outcome']]
    assert recorded_summary(args.timing_replay_log) == dict(expected_summary,
        benchmark_cases=5, timed_and_warmup_calls=50, eligible_cases=eligible)
    environment = json.loads(args.environment.read_bytes())
    assert type(environment) is dict and environment, 'missing benchmark environment record'

    tests = DATA/'factored-crushing-tests.txt'
    test_log = tests.read_text()
    assert re.search(r'Ran 238 tests in [0-9.]+s\s+OK\s*$', test_log)
    assert not re.search(r'\b(?:FAILED|ERROR|skipped)\b', test_log, re.IGNORECASE)
    command = DATA/'factored-crushing-test-command.txt'
    modules = set(re.findall(r'\btests\.(test_[A-Za-z0-9_]+)\b', command.read_text()))
    assert len(modules) == 25
    assert {'test_factored_crushing', 'test_factored_crushing_verify', 'test_interlace'} <= modules
    test_files = {ROOT/'fast/tests'/(name+'.py') for name in modules}
    assert all(path.is_file() for path in test_files)

    controls = DATA/'factored-crushing-corruption-controls.json'
    control_script = DATA/'factored-crushing-corruption-controls.py'
    control_fixture = DATA/'factored-crushing-corruption-fixture.json'
    corruption = json.loads(controls.read_bytes())
    assert corruption['passed'] is True and corruption['valid_control'] is True
    assert type(corruption['rejected_mutations']) is int and corruption['rejected_mutations'] == 19
    assert corruption['source_sha256'] == pins
    assert corruption['script_sha256'] == file_digest(control_script)
    assert corruption['fixture_sha256'] == file_digest(control_fixture)
    assert len(corruption['records']) == 19 and len({r['name'] for r in corruption['records']}) == 19
    assert all(r['rejected'] is True for r in corruption['records'])

    build_logs = [DATA/f'factored-crushing-latex-{i}.txt' for i in (1, 2, 3)]
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
    assert r'\input{factored_crushing.tex}' in includes.read_text()
    report_tex = ROOT/'synthesis/report.tex'
    tex = included_tex(report_tex)
    assert ROOT/'synthesis/factored_crushing.tex' in tex

    required = {args.audit.resolve(), args.benchmark.resolve(), args.environment.resolve(),
        args.replay_log.resolve(), args.timing_replay_log.resolve(), tests, command, *build_logs,
        controls, control_script, control_fixture, pdf, includes, report_tex, Path(__file__).resolve(),
        ROOT/'synthesis/factored_crushing.tex', ROOT/'synthesis/README.md', ROOT/'fast/README.md'}
    for name in ('factored-crushing-audit.txt', 'factored-crushing-benchmark.txt'):
        path = DATA/name
        assert path.read_text().rstrip().endswith('PASSED'), 'unfinished discovery/timing log: '+name
        required.add(path)
    assert all(path.is_file() for path in required)
    files = python_dependencies({ROOT/name for name in pins} | test_files | required | tex)
    files.update(path for path in DATA.glob('factored-crushing-*') if path.is_file())
    files.discard(args.output.resolve())
    files.discard(DATA/'factored-crushing-publication.json')
    # Exclude the stdout log that the caller may still be writing now.
    files.discard(DATA/'factored-crushing-publication.txt')
    assert all(path.is_relative_to(ROOT) for path in files)
    assert source_hashes() == pins, 'source changed during publication replay'
    manifest = dict(schema='factored-crushing-publication-v1', passed=True,
        general_quasipolynomial=False,
        restricted_visible_factor_quasipolynomial=True,
        restricted_visible_factor_scope='Conditional on polylogarithmic largest visible crossing block; explicit tree/source/polynomial-LP policy with all nine operational caps removed gives poly(n+1)*2**O(s). This is not a general bound or a theorem about the finite-cap transversal benchmark policy.',
        measured_scope='Whole-diagram raw versus factored native crushing under identical shared finite work allowances; all returned proofs and partial chains independently replayed.',
        counter_scope='Recorded nonnegative counter bounds and independently recomputed child/whole sums and peaks; no independent replay of the discovery LP operation trace.',
        source_pins_verified=True, discovery_run_by_this_helper=False,
        audit=dict(ordinary_cases=8, ordinary_calls=16, scaling_calls=4, total_calls=20,
                   outcomes={arm: dict(Counter(statuses)) for arm, statuses in outcomes.items()},
                   scaling_outcomes=[r['result']['status'] for r in audit['scaling']]),
        benchmark=dict(cases=5, timed_and_warmup_calls=50, eligible_cases=eligible,
            inconclusive_calls=sum(r['warmups'][arm]['status'] == 'INCONCLUSIVE'
                for r in benchmark['records'] for arm in ARMS)+
                sum(p['samples'][arm]['status'] == 'INCONCLUSIVE' for r in benchmark['records']
                    for p in r['paired'] for arm in ARMS)+
                sum(s['status'] == 'INCONCLUSIVE' for r in benchmark['records'] for s in r['aa']['samples'])),
        tests=238, test_modules=25, skipped_tests=0, rejected_corruption_controls=19,
        report_pages=int(match[1]), report_bytes=len(pdf_bytes), included_tex_files=len(tex),
        replayed_source_sha256=pins,
        files_sha256={str(path.relative_to(ROOT)): file_digest(path) for path in sorted(files)})
    assert source_hashes() == pins, 'source changed while hashing publication'
    args.output.write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps(dict(passed=True, ordinary_calls=16, scaling_calls=4, benchmark_calls=50,
        tests=238, rejected_corruption_controls=19, general_quasipolynomial=False,
        restricted_visible_factor_quasipolynomial=True, pinned_files=len(files)), sort_keys=True))


if __name__ == '__main__':
    main()
