"""Authenticate linear-contraction and port-bitset evidence; independently replay proofs."""
import argparse
from contextlib import ExitStack
from hashlib import sha256
import json
from pathlib import Path
import re
import statistics
import sys
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'synthesis/data'
REPO = ROOT.parents[1]
sys.path.insert(0, str(ROOT/'fast'))
from fastunknot.normal_prism_interfaces_verify import verify_normal_prism_interfaces


def read(name):
    return json.loads((DATA/name).read_text())


def authenticate(pins, root):
    for path, digest in pins.items():
        assert sha256((root/path).read_bytes()).hexdigest() == digest, path


def measurements(record, reference, alternative, control):
    authenticate(record['source_sha256'], REPO)
    for name in record['details']:
        rows = [r for r in record['samples'] if r['case'] == name]
        digest_field = 'structure_sha256' if 'structure_sha256' in rows[0] else 'result_sha256'
        assert len({r[digest_field] for r in rows}) == 1, name
        assert len(rows) == 18, (name, len(rows))
        for arm in (reference, alternative, control):
            selected = [r for r in rows if r['arm'] == arm]
            assert sorted(r['round'] for r in selected) == list(range(6))
            assert all(r['warmup'] == (r['round'] == 0) and r['seconds'] > 0 for r in selected)
            expected = statistics.median(r['seconds'] for r in selected if not r['warmup'])
            assert record['summary'][name]['median_seconds'][arm] == expected
        def ratio(other):
            return statistics.median(next(r['seconds'] for r in rows if r['arm'] == reference and r['round'] == i) /
                                     next(r['seconds'] for r in rows if r['arm'] == other and r['round'] == i)
                                     for i in range(1, 6))
        ratio_field = 'paired_vector_over_auto' if reference == 'vector' else 'paired_sorted_over_sweep'
        assert record['summary'][name][ratio_field] == ratio(alternative)
        assert record['summary'][name]['paired_identical_control'] == ratio(control)
    return len(record['samples'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--publication', action='store_true')
    args = parser.parse_args()
    audit = read('prism-port-encoding-audit.json')
    assert audit['supplied_cases'] == audit['previous_unattached_counts_preserved'] == len(audit['records']) == 5289
    assert len(audit['source_proofs']) == 58
    authenticate(audit['native_source_sha256'], ROOT)
    assert audit['pilot_sha256'] == sha256((DATA/'cut-product-pilot.json').read_bytes()).hexdigest()
    legacy = read('prism-interfaces-audit.json')
    assert [r['id'] for r in audit['source_proofs']] == [r['id'] for r in legacy['source_proofs']]
    for old, new in zip(legacy['source_proofs'], audit['source_proofs']):
        assert old['certificate']['structure'] == new['certificate']['structure']
    with ExitStack() as stack:
        for name in ('fastunknot.normal_prism_interfaces._interface_system',
                     'fastunknot.normal_prism_interfaces._profiles',
                     'fastunknot.weighted_orbits.weighted_orbit_histogram',
                     'fastunknot.interval_orbits.count_orbits'):
            stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
        for bank in (legacy, audit):
            for row in bank['source_proofs']:
                assert verify_normal_prism_interfaces(row['triangulation'], row['coordinates'], row['certificate'])
    for name, count, skipped in (('weighted-sweep-tests.txt', 1574, 8),
                                ('prism-port-encoding-tests.txt', 1579, 8),
                                ('prism-port-encoding-focused.txt', 21, 0)):
        log = (DATA/name).read_text()
        suffix = r'OK \(skipped=' + str(skipped) + r'\)' if skipped else 'OK'
        assert re.search(r'Ran ' + str(count) + r' tests in [0-9.]+s\n\n' + suffix, log), name
    contraction = read('weighted-sweep-benchmark.json')
    encoding = read('prism-port-encoding-benchmark.json')
    samples = measurements(contraction, 'sorted', 'sweep', 'sorted_control')
    samples += measurements(encoding, 'vector', 'auto', 'vector_control')
    result = dict(source_pins=len(audit['native_source_sha256']), supplied_structures=5289,
                  saved_legacy_proofs=58, saved_current_proofs=58, producers_disabled=True,
                  suite_tests=1579, suite_skipped=8, final_focused_tests=21,
                  measurement_samples=samples, ribbon_01_profiles_only=True,
                  ordered_boundary_curves=False, recognizer_integration=False,
                  general_quasipolynomial_recognition=False)
    if args.publication:
        log = (ROOT/'synthesis/report.log').read_text()
        assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error', log)
        warnings = re.findall(r'Overfull \\hbox \(([^)]*)\)', log)
        assert warnings == [f'{x}pt too wide' for x in ('12.64871', '13.49065', '9.04614', '35.14671')], warnings
        visual = read('weighted-prism-visual-review.json')
        assert visual['pdf_sha256'] == sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
        aux = (ROOT/'synthesis/report.aux').read_text()
        start = int(re.search(r'\\newlabel\{sec:weighted-sweep\}\{\{159\}\{(\d+)\}', aux).group(1))
        end = int(re.search(r'\\newlabel\{sec:prism-port-encoding\}\{\{160\}\{(\d+)\}', aux).group(1))
        toc = (ROOT/'synthesis/report.toc').read_text()
        assessment = int(re.search(r'\\numberline \{161\}Assessment and recommendations\}\{(\d+)\}', toc).group(1))
        assert visual['inspected_pages'] == list(range(start, assessment + 3))
        result.update(pdf_pages=int(re.search(r'Output written on report.pdf \((\d+) pages,', log).group(1)),
                      sweep_page=start, bitset_page=end, assessment_page=assessment,
                      preexisting_overfull_warnings=warnings, visual_review=visual)
    paths = [Path(__file__), DATA/'prism-port-encoding-audit.json', DATA/'weighted-sweep-benchmark.json',
             DATA/'prism-port-encoding-benchmark.json', DATA/'weighted-sweep-tests.txt',
             DATA/'prism-port-encoding-tests.txt', DATA/'prism-port-encoding-focused.txt',
             ROOT/'synthesis/weighted_sweep.tex', ROOT/'synthesis/prism_port_encoding.tex',
             ROOT/'synthesis/report.tex', ROOT/'synthesis/report.pdf',
             DATA/'weighted_prism_tables.py', ROOT/'synthesis/make_tables.py',
             ROOT/'synthesis/tables/weighted_sweep.tex', ROOT/'synthesis/tables/prism_port_encoding.tex',
             ROOT/'README.md', ROOT/'fast/README.md', ROOT/'synthesis/README.md']
    result['evidence_sha256'] = {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest() for p in paths}
    output = 'weighted-prism-publication-review.json' if args.publication else 'weighted-prism-runtime-review.json'
    (DATA/output).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('evidence_sha256', 'visual_review')}, indent=2))


if __name__ == '__main__':
    main()
