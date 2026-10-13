"""Replay and pin the complete inverse-layer publication; no discovery or timing.

Run from any directory with Python's normal assertions enabled. Supplied-source
reductions remain conditional workloads, separate from authenticated diagram
recognition. Historical publication manifests are never checked as current pins.
"""

import argparse
import ast
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
DATA = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'fast'))

from boundary_unlayer_research.common import source_hashes
from boundary_unlayer_research.replay import replay
from boundary_unlayer_research.timing_replay import replay_timings


def file_digest(path):
    return sha256(path.read_bytes()).hexdigest()


def recorded_summary(path):
    """Read a checker CLI's final JSON line, preserving preceding diagnostics."""
    lines = [line for line in path.read_text().splitlines() if line.strip()]
    assert lines, 'empty replay log: '+str(path)
    result = json.loads(lines[-1])
    assert type(result) is dict and result.get('passed') is True
    return result


def python_dependencies(paths):
    """Pin local static import dependencies and imported package initializers."""
    fast = ROOT/'fast'
    pending = [path for path in paths if path.suffix == '.py' and path.is_relative_to(fast)]
    visited, found = set(), set(paths)

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
        relative = path.relative_to(fast).with_suffix('')
        package = list(relative.parts[:-1])
        for node in ast.walk(ast.parse(path.read_text(), filename=str(path))):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    add_module(alias.name)
            elif isinstance(node, ast.ImportFrom):
                if node.level:
                    assert node.level <= len(package)+1
                    prefix = package[:len(package)-node.level+1]
                else:
                    prefix = []
                name = '.'.join(prefix+([node.module] if node.module else []))
                add_module(name)
                for alias in node.names:
                    if alias.name != '*':
                        add_module('.'.join(part for part in (name, alias.name) if part))
    return found


def main():
    if not __debug__:
        raise RuntimeError('publication replay requires Python assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', type=Path, default=DATA/'boundary-unlayer-audit.json')
    parser.add_argument('--benchmark', type=Path, default=DATA/'boundary-unlayer-benchmark.json')
    parser.add_argument('--environment', type=Path, default=DATA/'boundary-unlayer-environment.json')
    parser.add_argument('--replay-log', type=Path, default=DATA/'boundary-unlayer-replay.txt')
    parser.add_argument('--timing-replay-log', type=Path, default=DATA/'boundary-unlayer-timing-replay.txt')
    parser.add_argument('--output', type=Path, default=DATA/'boundary-unlayer-publication.json')
    args = parser.parse_args()

    pins = source_hashes()
    raw = args.audit.read_bytes()
    audit = json.loads(raw)
    audit_summary = replay(audit, with_regina=False, allow_partial=False)
    expected = dict(passed=True, inverse_families=9, inverse_steps=42,
                    supplied_comparisons=18, diagrams=3, regina_used=False,
                    full_coverage=True)
    assert audit_summary == expected, 'incomplete or unexpected audit coverage'
    supplied = [arm for record in audit['supplied_reductions'] for arm in record['arms'].values()]
    diagrams = [arm for record in audit['diagrams'] for arm in record['arms'].values()]
    assert len(supplied) == 36 and len(diagrams) == 6
    assert all(arm['outcome'] in ('TERMINAL_NO_TORUS_COMPONENT',
               'COMPLETE_NEGATIVE_ENDPOINT', 'INCONCLUSIVE') for arm in supplied)
    assert Counter(arm['result']['status'] for arm in diagrams) == {'UNKNOT': 2, 'KNOTTED': 4}
    assert recorded_summary(args.replay_log) == audit_summary

    benchmark = json.loads(args.benchmark.read_text())
    timing_summary = replay_timings(benchmark, audit, raw)
    assert timing_summary == dict(passed=True, cases=6, samples=60, regina_used=False)
    assert recorded_summary(args.timing_replay_log) == timing_summary
    environment = json.loads(args.environment.read_text())
    assert type(environment) is dict and environment, 'missing timing environment record'

    tests = DATA/'boundary-unlayer-tests.txt'
    test_log = tests.read_text()
    assert re.search(r'Ran 208 tests in [0-9.]+s\s+OK\s*$', test_log)
    assert not re.search(r'\b(?:FAILED|ERROR|skipped)\b', test_log, re.IGNORECASE)
    command = DATA/'boundary-unlayer-test-command.txt'
    modules = set(re.findall(r'\btests\.(test_[A-Za-z0-9_]+)\b', command.read_text()))
    assert 'test_boundary_unlayer' in modules and len(modules) >= 22
    test_files = {ROOT/'fast/tests'/str(name+'.py') for name in modules}
    assert all(path.is_file() for path in test_files)

    build_logs = [DATA/f'boundary-unlayer-latex-{i}.txt' for i in (1, 2, 3)]
    for path in build_logs:
        assert 'Output written on report.pdf' in path.read_text(), 'failed PDF pass: '+path.name
    last_build = build_logs[-1].read_text()
    assert not re.search(r'undefined references|undefined on input|Rerun to get|Label\(s\) may have changed', last_build)
    match = re.search(r'Output written on report\.pdf \((\d+) pages, (\d+) bytes\)', last_build)
    assert match, 'missing final PDF build size'
    pdf = ROOT/'synthesis/report.pdf'
    pdf_bytes = pdf.read_bytes()
    assert pdf_bytes.startswith(b'%PDF-') and len(pdf_bytes) == int(match[2])
    includes = ROOT/'synthesis/marked_cut_handlebodies.tex'
    assert r'\input{boundary_unlayer.tex}' in includes.read_text()

    required = {args.audit.resolve(), args.benchmark.resolve(), args.environment.resolve(),
                args.replay_log.resolve(), args.timing_replay_log.resolve(),
                tests, command, *build_logs, pdf, includes, Path(__file__).resolve(),
                ROOT/'fast/README.md', ROOT/'synthesis/README.md', ROOT/'synthesis/report.tex',
                ROOT/'synthesis/boundary_unlayer.tex', ROOT/'synthesis/boundary_transversal.tex'}
    for name in ('boundary-unlayer-audit.txt', 'boundary-unlayer-benchmark.txt'):
        path = DATA/name
        assert path.read_text().rstrip().endswith('PASSED'), 'unfinished run log: '+name
        required.add(path)
    # The combined report may include the separately replayed connected-sum
    # evidence. Bind that saved replay to its current source pins without
    # implying that this helper reruns its original STANDARD rank audit.
    composition = None
    composition_pins = {}
    composition_article = ROOT/'synthesis/conflict_composition.tex'
    if r'\input{conflict_composition.tex}' in includes.read_text():
        from conflict_composition_research.common import source_hashes as composition_hashes
        composition_file = DATA/'conflict-composition-audit.json'
        saved = json.loads(composition_file.read_text())
        composition_pins = composition_hashes()
        assert saved['schema'] == 'conflict-composition-audit-v1' and saved['passed'] is True
        assert saved['source_sha256'] == composition_pins
        assert len(saved['witnesses']) == 35 and saved['tetrahedra'] == 23
        assert saved['hypergraph']['source_h_lower_bound'] == 5
        assert saved['hypergraph']['retained_hypergraph_transversal_number'] == 5
        assert saved['hypergraph']['four_subsets_excluded'] == 8855
        assert saved['hypergraph']['source_h_upper_bound'] is None
        assert saved['negative_cone_verified'] is False
        assert saved['complete_recognition_verdict'] is None
        assert saved['same_labelled_endpoint'] is True and saved['optional_unlayerings'] == 0
        required.update({composition_article, composition_file})
        required.update(path for path in DATA.glob('conflict-composition-*') if path.is_file())
        composition = dict(source_pins_verified=True, independent_replay_in_this_helper=False,
            witnesses=35, source_h_lower_bound=5, retained_hypergraph_transversal_number=5,
            source_h_upper_bound=None, negative_cone_verified=False,
            complete_recognition_verdict=None, optional_unlayerings=0)
    assert all(path.is_file() for path in required)
    files = python_dependencies({ROOT/name for name in pins | composition_pins} | test_files | required)
    files.update(path for path in DATA.glob('boundary-unlayer-*') if path.is_file())
    files.discard(args.output.resolve())
    files.discard(DATA/'boundary-unlayer-publication.json')
    # A shell may still be writing this checker's own stdout while we hash.
    files.discard(DATA/'boundary-unlayer-publication.txt')
    assert all(path.is_relative_to(ROOT) for path in files), 'publication files must be in the project'
    assert source_hashes() == pins, 'replayed sources changed during publication check'
    manifest = dict(schema='boundary-unlayer-publication-v1', passed=True,
        general_quasipolynomial=False,
        scope='Certified compact-manifold simplification and finite comparisons only; supplied-source reductions are conditional, separate from authenticated diagram verdicts.',
        supplied_source_verdicts_are_conditional=True, native_diagram_recognition_arms=6,
        audit=audit_summary, supplied_reduction_arms=36,
        supplied_outcomes=dict(sorted(Counter(arm['outcome'] for arm in supplied).items())),
        supplied_unreturned_queries=sum(arm['unreturned_query'] for arm in supplied),
        benchmark=timing_summary, tests=208, skipped_tests=0,
        benchmark_eligible_comparisons=[dict(kind=record['kind'], id=record['id'])
            for record in benchmark['records']
            if record['summary']['eligible_complete_comparison']],
        benchmark_inconclusive_samples=sum(sample['outcome'] is None
            for record in benchmark['records']
            for sample in record['warmups']+record['aa']['samples']+
                [s for pair in record['paired'] for s in pair['samples'].values()]),
        composition=composition,
        report_pages=int(match[1]), report_bytes=len(pdf_bytes),
        replayed_source_sha256=pins,
        files_sha256={str(path.relative_to(ROOT)): file_digest(path) for path in sorted(files)})
    assert source_hashes() == pins, 'sources changed while hashing publication'
    if composition_pins:
        assert composition_hashes() == composition_pins, 'composition sources changed while hashing publication'
    args.output.write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps(dict(passed=True, inverse_families=9, inverse_steps=42,
        supplied_reduction_arms=36, native_diagram_recognition_arms=6,
        benchmark_cases=6, timed_and_warmup_samples=60, tests=208,
        general_quasipolynomial=False, pinned_files=len(files)), sort_keys=True))


if __name__ == '__main__':
    main()
