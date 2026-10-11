"""Authenticate source-boundary cell evidence, replay proofs and review publication."""
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
DATA = ROOT/'synthesis/data'
REPO = ROOT.parents[1]
sys.path.insert(0, str(ROOT/'fast'))
from fastunknot.normal_cut_boundary_verify import verify_normal_cut_boundary


def read(name): return json.loads((DATA/name).read_text())
def pins(values, root):
    for path, digest in values.items(): assert sha256((root/path).read_bytes()).hexdigest() == digest, path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--publication', action='store_true'); args = parser.parse_args()
    audit = read('cut-boundary-audit.json'); benchmark = read('cut-boundary-benchmark.json')
    assert audit['finite_cases'] == len(audit['records']) == 1755
    assert audit['pilot_cases'] == 1635 and audit['oriented_edge_incidences'] == 340202
    assert len(audit['large_binary_cases']) == 10 and len(audit['source_proofs']) == 110
    assert sum(any(p[0] > 1 for p in r['piece_types']) for r in audit['records']) == 45
    pins(audit['native_source_sha256'], ROOT); pins(benchmark['source_sha256'], REPO)
    assert audit['pilot_sha256'] == sha256((DATA/'complement-chamber-pilot.json').read_bytes()).hexdigest()
    assert audit['corpus_sha256'] == sha256((ROOT/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest()
    assert audit['sphere_boundary_obstruction'] == dict(source_id='solid_torus_sum_rp3', standard_vertex=6,
        boundary_components=1, total_boundary_genus=0, regina_is_ball=False, regina_homology='Z_2')
    environment = read('cut-boundary-oracle-environment.json')
    assert environment['distribution_version'] == '7.4.1' and environment['engine_version'] == audit['regina_version'] == benchmark['regina_version'] == '7.4'
    assert re.search(r'Ran 1589 tests in [0-9.]+s\n\nOK\n', (DATA/'cut-boundary-tests.txt').read_text())
    disabled = ('fastunknot.normal_cut_boundary._boundary_system', 'fastunknot.normal_cut_boundary._cycle_recipes',
                'fastunknot.normal_cut_boundary._boundary_summary', 'fastunknot.normal_cut_boundary._piece_summary',
                'fastunknot.normal_cut_boundary.normal_cut_boundary', 'fastunknot.normal_cut_complement._chamber_system',
                'fastunknot.orbit_transversal.orbit_transversal', 'fastunknot.orbit_transversal._forward_selector',
                'fastunknot.weighted_orbits.weighted_orbit_histogram',
                'fastunknot.weighted_orbits.weighted_histogram_from_orbit_certificate', 'fastunknot.interval_orbits.count_orbits')
    with ExitStack() as stack:
        for name in disabled: stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
        for r in audit['source_proofs']:
            assert verify_normal_cut_boundary(r['triangulation'], r['coordinates'], r['certificate']), r['id']
            g = r['certificate']['geometry']; t = len(r['coordinates'])
            assert len(g['faces']) <= 30*t and len(g['edges']) <= 138*t and len(g['vertices']) <= 16*t and len(g['carriers']) <= 42*t
    assert len(benchmark['samples']) == 126
    for name, summary in benchmark['summary'].items():
        rows = [r for r in benchmark['samples'] if r['case'] == name]
        assert len(rows) == 18 and all(r['complete'] for r in rows)
        assert len({r['profile_sha256'] for r in rows}) == 1
        for arm in ('regina', 'regina_control', 'native'):
            selected = [r for r in rows if r['arm'] == arm]
            assert sorted(r['round'] for r in selected) == list(range(6))
            assert all(r['warmup'] == (r['round'] == 0) and r['seconds'] > 0 for r in selected)
            assert summary['median_seconds'][arm] == statistics.median(r['seconds'] for r in selected if not r['warmup'])
        def ratio(other):
            return statistics.median(next(r['seconds'] for r in rows if r['arm'] == 'regina' and r['round'] == i) /
                                     next(r['seconds'] for r in rows if r['arm'] == other and r['round'] == i) for i in range(1, 6))
        assert summary['paired_regina_over_native'] == ratio('native') and summary['identical_control'] == ratio('regina_control')
    result = dict(source_pins=len(audit['native_source_sha256']), maintained_tests=1589, maintained_skips=0,
                  finite_cases=1755, pilot_cases=1635, multiple_boundary_cases=45, oriented_edge_incidences=340202,
                  producer_disabled_proofs=110, binary_cases=10, measured_samples=105, warmup_samples=21,
                  sphere_boundary_nonball_verified=True, full_boundary_cells=True, full_interior_cells=False,
                  pattern_transport=False, general_quasipolynomial_recognition=False)
    if args.publication:
        log = (ROOT/'synthesis/report.log').read_text()
        assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error', log)
        warnings = re.findall(r'Overfull \\hbox \(([^)]*)\)', log)
        assert warnings == [f'{x}pt too wide' for x in ('12.64871', '13.49065', '9.04614', '35.14671')], warnings
        aux = (ROOT/'synthesis/report.aux').read_text(); toc = (ROOT/'synthesis/report.toc').read_text()
        first = int(re.search(r'\\newlabel\{sec:cut-boundary\}\{\{161\}\{(\d+)\}', aux).group(1))
        assessment = int(re.search(r'\\numberline \{162\}Assessment and recommendations\}\{(\d+)\}', toc).group(1))
        visual = read('cut-boundary-visual-review.json')
        assert visual['pdf_sha256'] == sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
        assert visual['inspected_pages'] == list(range(first, assessment+3))
        result.update(pdf_pages=int(re.search(r'Output written on report.pdf \((\d+) pages,', log).group(1)),
                      section_page=first, assessment_page=assessment, visual_review=visual, preexisting_overfull_warnings=warnings)
    paths = [Path(__file__), DATA/'cut_boundary_tables.py', DATA/'cut-boundary-audit.json',
             DATA/'cut-boundary-benchmark.json', DATA/'cut-boundary-tests.txt', DATA/'cut-boundary-oracle-environment.json',
             ROOT/'synthesis/cut_boundary.tex', ROOT/'synthesis/tables/cut_boundary.tex', ROOT/'synthesis/make_tables.py',
             ROOT/'synthesis/report.tex', ROOT/'synthesis/report.pdf', ROOT/'README.md', ROOT/'fast/README.md', ROOT/'synthesis/README.md']
    result['evidence_sha256'] = {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest() for p in paths}
    name = 'cut-boundary-publication-review.json' if args.publication else 'cut-boundary-runtime-review.json'
    (DATA/name).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('evidence_sha256', 'visual_review')}, indent=2))


if __name__ == '__main__': main()
