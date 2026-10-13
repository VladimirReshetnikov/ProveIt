"""Verify final test/build artifacts; run no tests, discovery, replay or timing.

The pre-run snapshot contains ``files_sha256`` and ``expected_tests``.  Its
file map is exactly ``test_source_files()``; historical pins are not current
source claims.  Run from any directory after all final artifacts exist.
"""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re

from strict_pachner32_publication import included_tex, python_dependencies

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
PREFIX = 'direct-crush-positive'
COMMAND = DATA/f'{PREFIX}-test-command.txt'
HISTORICAL_COMMIT = '3d3498207'
HISTORICAL_MANIFEST_SHA256 = '77d7cd49880b6352370ea598e15510c954490f52c5d61d0e22a1aeb73183df01'


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def test_source_files():
    """Exact pre-run native/static-test/dynamic-fixture/command byte map."""
    names = re.findall(r'\btests\.(test_[A-Za-z0-9_]+)\b', COMMAND.read_text())
    assert len(names) == len(set(names)) == 43
    tests = {ROOT/'fast/tests'/(name+'.py') for name in names}
    initializer = ROOT/'fast/tests/__init__.py'
    if initializer.is_file():
        tests.add(initializer)
    fixtures = {DATA/'boundary-unlayer-audit.json',
        DATA/'coherent-obstruction-certificate.json',
        ROOT/'reports/79/repro/fast/commitment_research/coherent-obstruction-certificate.json',
        ROOT/'reports/79/repro/fast/shared_cover_research/results/exhaustion.json',
        ROOT/'fast/tests/fixtures/causal_noncanonical.json',
        ROOT/'fast/conflict_composition_research/data/generation/tt-state.json.gz',
        ROOT/'fast/strict_pachner32_research/data/generation/euler-queries.json.gz'}
    files = set((ROOT/'fast/fastunknot').rglob('*.py'))
    files.update(python_dependencies(tests | fixtures))
    files.add(COMMAND)
    assert all(p.is_file() and p.is_relative_to(ROOT) for p in files)
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(files)}


def diagnostics(contents):
    result = Counter()
    for line in contents.splitlines():
        if 'Warning:' in line or re.match(r'^(?:Over|Under)full \\[hv]box\b', line):
            line = re.sub(r'\bat lines \d+--\d+\b', 'at lines <range>', line.strip())
            line = re.sub(r'\bat line \d+\b', 'at line <number>', line)
            result[line] += 1
    return result


def main():
    if not __debug__:
        raise RuntimeError('publication verification requires assertions enabled')
    snapshot_path = DATA/f'{PREFIX}-test-source.json'
    snapshot = json.loads(snapshot_path.read_bytes())
    tested = test_source_files()
    assert type(snapshot['files_sha256']) is dict and snapshot['files_sha256'] == tested
    expected = snapshot['expected_tests']
    assert type(expected) is int and expected > 0
    log_path = DATA/f'{PREFIX}-tests.txt'
    log = log_path.read_text()
    ran = re.findall(r'^Ran (\d+) tests in [\d.]+s$', log, re.MULTILINE)
    assert ran == [str(expected)] and log.rstrip().endswith('\nOK')
    assert not re.search(r'skipped|expected failure|unexpected success|^FAIL|^ERROR', log, re.I | re.M)
    cases = re.findall(r'^test_\w+ \((tests\.[^\n)]+)\) \.\.\. ok$', log, re.M)
    assert len(cases) == len(set(cases)) == expected
    observed = {case.split('.')[1] for case in cases}
    modules = set(re.findall(r'\btests\.(test_[A-Za-z0-9_]+)\b', COMMAND.read_text()))
    assert observed == modules and len(observed) == 43

    historical_path = DATA/'geometric-descent-evidence-publication.json'
    assert digest(historical_path) == HISTORICAL_MANIFEST_SHA256
    historical = json.loads(historical_path.read_bytes())
    baseline = DATA/'geometric-descent-evidence-latex-3.txt'
    assert digest(baseline) == historical['files_sha256'][str(baseline.relative_to(ROOT))]
    builds = [DATA/f'{PREFIX}-latex-{i}.txt' for i in (1, 2, 3)]
    for path in builds:
        contents = path.read_text()
        assert 'Output written on report.pdf' in contents
        assert not re.search(r'^!|Emergency stop|Fatal error occurred', contents, re.M)
    final = builds[-1].read_text()
    assert not re.search(r'undefined references|undefined on input|Rerun to get|Label\(s\) may have changed|multiply.defined labels', final)
    assert not (diagnostics(final)-diagnostics(baseline.read_text()))
    match = re.search(r'Output written on report\.pdf \((\d+) pages, (\d+) bytes\)', final)
    assert match
    pdf = ROOT/'synthesis/report.pdf'
    assert pdf.read_bytes().startswith(b'%PDF-') and pdf.stat().st_size == int(match[2])
    tex = included_tex(ROOT/'synthesis/report.tex')
    assert ROOT/'synthesis/direct_crush_positive.tex' in tex

    files = {ROOT/name for name in tested} | tex | set(builds) | {
        Path(__file__).resolve(), snapshot_path, log_path, pdf,
        ROOT/'fast/README.md', ROOT/'synthesis/README.md', historical_path, baseline,
        DATA/'strict_pachner32_publication.py',
        # The imported walkers' only nonstdlib imports; retain their closure.
        ROOT/'fast/strict_pachner32_research/common.py',
        ROOT/'fast/strict_pachner32_research/check_evidence.py'}
    files = python_dependencies(files)
    assert all(p.is_file() and p.is_relative_to(ROOT) for p in files)
    assert test_source_files() == tested, 'tested files changed during verification'
    result = dict(schema='direct-crush-positive-publication-v1', passed=True,
        tests=expected, test_modules=43, skipped_tests=0,
        test_native_files_byte_verified=True, pre_run_test_closure_exact=True,
        tested_files=len(tested), native_modules=len(list((ROOT/'fast/fastunknot').rglob('*.py'))),
        report_pages=int(match[1]), report_bytes=int(match[2]), included_tex_files=len(tex),
        general_quasipolynomial=False, new_timing_claims=False,
        tests_or_build_run_by_this_helper=False, certificate_replay_run_by_this_helper=False,
        historical_diagnostic_reference=dict(commit=HISTORICAL_COMMIT,
            manifest_sha256=HISTORICAL_MANIFEST_SHA256, baseline_sha256=digest(baseline)),
        files_sha256={str(p.relative_to(ROOT)): digest(p) for p in sorted(files)})
    (DATA/f'{PREFIX}-publication.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'files_sha256'}, sort_keys=True))


if __name__ == '__main__':
    main()
