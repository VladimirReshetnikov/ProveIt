"""Replay and pin the geometry-only first-descent core publication.

Run only after the retained 364-test regression and final three-pass PDF exist.
This helper runs the portable conditional-matching checker, but no discovery,
timing, tests, PDF build, or historical publication main().
"""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
sys.path.insert(0, str(ROOT/'fast'))

# Import only the deterministic walkers.  The historical helper's main() is
# never invoked, and none of its old evidence is treated as current evidence.
from strict_pachner32_publication import included_tex, python_dependencies
from conditional_type_research.common import canonical_bytes, source_hashes
from conditional_type_research.replay import check as check_conditional


def file_digest(path):
    return sha256(path.read_bytes()).hexdigest()


def same(actual, expected):
    """Exact JSON types and values, independent of dictionary insertion order."""
    return canonical_bytes(actual) == canonical_bytes(expected)


def diagnostics(text):
    """Compare diagnostic content and counts, ignoring shifted source lines."""
    result = Counter()
    for line in text.splitlines():
        if 'Warning:' not in line and not re.match(r'^(?:Over|Under)full \\[hv]box\b', line):
            continue
        line = re.sub(r'\bat lines \d+--\d+\b', 'at lines <range>', line.strip())
        line = re.sub(r'\bat line \d+\b', 'at line <number>', line)
        result[line] += 1
    return result


def main():
    if not __debug__:
        raise RuntimeError('publication checks require assertions enabled')

    command = DATA/'geometric-descent-test-command.txt'
    modules = set(re.findall(r'\btests\.(test_[A-Za-z0-9_]+)\b', command.read_text()))
    assert len(modules) == 41
    assert {'test_normal_geometric_descent', 'test_normal_geometric_descent_verify',
            'test_geometric_descent_crushing', 'test_normal_pachner_descent',
            'test_normal_pachner_descent_verify', 'test_pachner_descent_crushing',
            'test_factored_crushing', 'test_factored_crushing_verify'} <= modules
    test_log = DATA/'geometric-descent-tests.txt'
    contents = test_log.read_text()
    assert re.search(r'Ran 364 tests in [0-9.]+s\s+OK\s*$', contents)
    assert not re.search(r'\b(?:FAILED|ERROR|skipped)\b', contents, re.IGNORECASE)
    observed = set(re.findall(r'\(tests\.(test_[A-Za-z0-9_]+)\.', contents))
    assert observed == modules, 'retained regression does not cover exactly the declared modules'
    test_files = {ROOT/'fast/tests'/(name+'.py') for name in modules}
    assert all(path.is_file() for path in test_files)

    # Freshly re-execute solver-free source-chain and original STANDARD replay.
    # Generation pins inside the exact archived groups remain historical.
    retained_path = DATA/'conditional-type-matching-replay.json'
    retained_log = DATA/'conditional-type-matching-replay.txt'
    retained = json.loads(retained_path.read_bytes())
    fresh = check_conditional()
    assert same(fresh, retained), 'retained conditional replay differs from fresh replay'
    pins = fresh['source_sha256']
    assert len(pins) == 326 and same(pins, source_hashes())
    assert same(fresh['archive_bytes'], dict(experiment_groups=2,
        original_manifest_files=2, preserved_group_files=16, staged_source_archives=1))
    assert fresh['source_bindings_between_experiments'] == 6
    cheap, exact = fresh['cheap_closure'], fresh['exact_witnesses']
    assert same({key: cheap[key] for key in ('attempted_queries', 'returned_queries',
        'capped_queries', 'deleted_types', 'conditional_provenance_packets',
        'construction_checks', 'other_forced_deletion_controls')},
        dict(attempted_queries=216, returned_queries=215, capped_queries=1,
             deleted_types=0, conditional_provenance_packets=0,
             construction_checks=1594870, other_forced_deletion_controls=0))
    assert exact['verified_matching_witnesses'] == 276 and exact['completed_sources'] == 6
    assert exact['construction_checks'] == 111348
    assert exact['all_initial_conditional_types_feasible'] is True
    controls = exact['rejected_corruption_controls']
    assert len(controls) == len({item['name'] for item in controls}) == 12
    assert all(item['rejected'] is True for item in controls)
    assert fresh['discovery_used'] is False and fresh['timing_claim'] is False
    assert fresh['native_conditional_elimination_added'] is False
    assert fresh['general_quasipolynomial'] is False
    lines = [line for line in retained_log.read_text().splitlines() if line.strip()]
    assert len(lines) == 1
    expected_summary = dict(passed=True, experiment_groups=2,
        cheap_attempted_queries=216, cheap_returned_queries=215, cheap_capped_queries=1,
        global_deletions=0, exact_matching_witnesses=276, source_bindings=6,
        rejected_corruption_controls=12, source_pins=326,
        discovery_used=False, general_quasipolynomial=False)
    assert same(json.loads(lines[0]), expected_summary)

    builds = [DATA/f'geometric-descent-latex-{index}.txt' for index in (1, 2, 3)]
    for path in builds:
        log = path.read_text()
        assert 'Output written on report.pdf' in log, 'failed PDF pass: '+path.name
        assert not re.search(r'^!|Emergency stop|Fatal error occurred', log, re.MULTILINE)
    final = builds[-1].read_text()
    assert not re.search(r'undefined references|undefined on input|Rerun to get|'
                         r'Label\(s\) may have changed|multiply.defined labels', final)
    # The previous final build is used only as a historical formatting-warning
    # baseline.  Its PDF size, TeX pins and publication claims are not reused.
    warning_baseline = DATA/'pachner-descent-latex-3.txt'
    known = diagnostics(warning_baseline.read_text())
    actual = diagnostics(final)
    assert not (actual-known), 'new final-build diagnostic: '+repr(actual-known)
    known_overfull = Counter({line: count for line, count in known.items()
                             if line.startswith('Overfull ')})
    actual_overfull = Counter({line: count for line, count in actual.items()
                              if line.startswith('Overfull ')})
    assert sum(known_overfull.values()) == 4
    assert actual_overfull == known_overfull, 'historical four-overflow baseline changed'
    match = re.search(r'Output written on report\.pdf \((\d+) pages, (\d+) bytes\)', final)
    assert match, 'missing final PDF page and byte count'
    pdf = ROOT/'synthesis/report.pdf'
    pdf_bytes = pdf.read_bytes()
    assert pdf_bytes.startswith(b'%PDF-') and len(pdf_bytes) == int(match[2])
    tex = included_tex(ROOT/'synthesis/report.tex')
    assert {ROOT/'synthesis/geometric_descent_crushing.tex',
            ROOT/'synthesis/conditional_type_matching.tex'} <= tex

    files = {Path(__file__).resolve(), DATA/'strict_pachner32_publication.py',
        command, test_log, retained_path, retained_log, warning_baseline,
        pdf, ROOT/'fast/README.md', ROOT/'synthesis/README.md', *builds, *tex, *test_files}
    files.update(ROOT/name for name in pins)
    files.update((ROOT/'fast/fastunknot').rglob('*.py'))
    # Importing the historical walker module imports these definitions, but
    # does not run their old audit/checker main routines.  Include their static
    # import closure in the actual current helper dependency set.
    files.update((ROOT/'fast/strict_pachner32_research').glob('*.py'))
    # The exact seven serialized fixture dependencies retained by the previous
    # core helper.  Dynamic loading is not visible to the static import walker.
    files.update((DATA/'boundary-unlayer-audit.json',
                  DATA/'coherent-obstruction-certificate.json',
                  ROOT/'reports/79/repro/fast/commitment_research/coherent-obstruction-certificate.json',
                  ROOT/'reports/79/repro/fast/shared_cover_research/results/exhaustion.json',
                  ROOT/'fast/tests/fixtures/causal_noncanonical.json',
                  ROOT/'fast/conflict_composition_research/data/generation/tt-state.json.gz',
                  ROOT/'fast/strict_pachner32_research/data/generation/euler-queries.json.gz'))
    files = python_dependencies(files)
    assert all(path.is_file() and path.is_relative_to(ROOT) for path in files)
    output_path = DATA/'geometric-descent-publication.json'
    files.discard(output_path)
    files.discard(DATA/'geometric-descent-publication.txt')
    assert same(source_hashes(), pins), 'conditional replay dependencies changed'
    result = dict(schema='geometric-descent-core-publication-v1', passed=True,
        tests=364, test_modules=41, skipped_tests=0,
        geometric_first_descent_polynomial=True, fixed_total_upward_allowance=1,
        query_bit_bound='O(t^5 log^2(t+2))',
        repeated_preprocessing_bit_bound='O(t^6 log^2(t+2))',
        working_storage_bit_bound='O(t log(t+2))',
        accepted_packet_bit_bound='O(t log(t+2))',
        bound_scope='Conservative bounds for the actual fixed-depth D/UDD geometric preprocessing; arbitrary caller callback work is charged separately.',
        general_quasipolynomial=False, resolving_parameter_monotonicity_claimed=False,
        new_performance_measurement=False, discovery_run_by_this_helper=False,
        tests_or_pdf_build_run_by_this_helper=False,
        conditional_archival_replay=expected_summary,
        conditional_native_elimination_added=False,
        conditional_scope='Two exact historical experiments, freshly replayed on their same six source-authenticated endpoints; formal matching feasibility does not imply Euler positivity or global admissibility.',
        historical_scope='Embedded generation pins remain historical. The prior final TeX log supplies only the known formatting-diagnostic baseline; no historical publication main is invoked.',
        historical_overfull_boxes=4, new_final_build_diagnostics=0,
        report_pages=int(match[1]), report_bytes=len(pdf_bytes), included_tex_files=len(tex),
        conditional_source_sha256=pins,
        files_sha256={str(path.relative_to(ROOT)): file_digest(path) for path in sorted(files)})
    assert same(source_hashes(), pins), 'dependencies changed while hashing publication'
    output_path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(passed=True, tests=364, test_modules=41,
        conditional_matching_witnesses=276, rejected_corruption_controls=12,
        conditional_source_pins=326, pinned_files=len(files),
        report_pages=int(match[1]), new_performance_measurement=False,
        general_quasipolynomial=False), sort_keys=True))


if __name__ == '__main__':
    main()
