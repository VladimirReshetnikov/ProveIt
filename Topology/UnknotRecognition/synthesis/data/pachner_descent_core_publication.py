"""Pin the tested fixed-one-upward implementation and rebuilt theory article.

This records retained regression/build results. It runs no discovery, timing,
tests, or historical evidence publication helpers.
"""
from hashlib import sha256
import json
from pathlib import Path
import re

# Reuse only deterministic dependency walkers; importing this historical
# helper does not run its main routine or reinterpret its old evidence pins.
from strict_pachner32_publication import included_tex, python_dependencies


DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent


def main():
    if not __debug__:
        raise RuntimeError('publication checks require assertions enabled')
    command = DATA/'pachner-descent-test-command.txt'
    modules = set(re.findall(r'\btests\.(test_[A-Za-z0-9_]+)\b', command.read_text()))
    assert len(modules) == 38
    logs = [('pachner-descent-tests.txt', 336),
            ('pachner-descent-integration-tests.txt', 18),
            ('pachner-descent-verifier-final-tests.txt', 7)]
    files = {command, Path(__file__).resolve(), DATA/'strict_pachner32_publication.py'}
    for name, count in logs:
        path = DATA/name
        contents = path.read_text()
        assert re.search(r'Ran '+str(count)+r' tests in [0-9.]+s\s+OK\s*$', contents)
        assert not re.search(r'\b(?:FAILED|ERROR|skipped)\b', contents, re.I)
        files.add(path)
    builds = [DATA/f'pachner-descent-core-latex-{i}.txt' for i in (1, 2, 3)]
    for path in builds:
        assert 'Output written on report.pdf' in path.read_text()
    final = builds[-1].read_text()
    assert not re.search(r'undefined references|undefined on input|Rerun to get|Label\(s\) may have changed|multiply.defined labels', final)
    match = re.search(r'Output written on report\.pdf \((\d+) pages, (\d+) bytes\)', final)
    assert match
    pdf = ROOT/'synthesis/report.pdf'
    assert pdf.read_bytes().startswith(b'%PDF-') and pdf.stat().st_size == int(match[2])
    tex = included_tex(ROOT/'synthesis/report.tex')
    assert ROOT/'synthesis/pachner_descent_crushing.tex' in tex
    files.update(tex)
    files.update(builds)
    files.update((pdf, ROOT/'fast/README.md', ROOT/'synthesis/README.md'))
    files.update((ROOT/'fast/fastunknot').rglob('*.py'))
    files.update((ROOT/'fast/strict_pachner32_research').glob('*.py'))
    files.update(ROOT/'fast/tests'/(name+'.py') for name in modules)
    # Explicit serialized fixture dependencies; historical source pin maps in
    # these inputs keep their original meaning.
    files.update((DATA/'boundary-unlayer-audit.json',
                  DATA/'coherent-obstruction-certificate.json',
                  ROOT/'fast/conflict_composition_research/data/generation/tt-state.json.gz',
                  ROOT/'fast/strict_pachner32_research/data/generation/euler-queries.json.gz'))
    files = python_dependencies(files)
    assert all(path.is_file() and path.is_relative_to(ROOT) for path in files)
    output = dict(schema='pachner-descent-core-publication-v1', passed=True,
        general_quasipolynomial=False, fixed_one_upward_preprocessing_polynomial=True,
        new_performance_measurement=False, discovery_run_by_this_helper=False,
        tests=336, test_modules=38, final_focused_verifier_tests=7, skipped_tests=0,
        test_scope='The broad regression was followed by a focused verifier rerun after strengthening an outer-successor mutation assertion; native code stayed unchanged.',
        report_pages=int(match[1]), report_bytes=int(match[2]), included_tex_files=len(tex),
        files_sha256={str(path.relative_to(ROOT)): sha256(path.read_bytes()).hexdigest()
                      for path in sorted(files)})
    (DATA/'pachner-descent-core-publication.json').write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(dict(passed=True, tests=336, final_focused_verifier_tests=7,
        pinned_files=len(files), report_pages=int(match[1]), general_quasipolynomial=False), sort_keys=True))


if __name__ == '__main__':
    main()
