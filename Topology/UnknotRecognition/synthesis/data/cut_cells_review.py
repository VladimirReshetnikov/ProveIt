"""Authenticate full raw-cut cells, independent homology evidence and publication."""
import argparse
from contextlib import ExitStack
from hashlib import sha256
import json
from pathlib import Path
import re
import statistics
import subprocess
import sys
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]; DATA = ROOT/'synthesis/data'; REPO = ROOT.parents[1]
sys.path.insert(0, str(ROOT/'fast'))
from fastunknot.normal_cut_cells_verify import verify_normal_cut_cell_complex

def read(name): return json.loads((DATA/name).read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument('--publication', action='store_true'); args = parser.parse_args()
    audit = read('cut-cells-audit.json'); benchmark = read('cut-cells-benchmark.json')
    assert audit['finite_cases'] == len(audit['records']) == 1755 and audit['pilot_cases'] == 1635
    assert audit['integral_zero_checks'] == 233036 and audit['edge_face_incidences'] == 638563 and audit['face_chamber_incidences'] == 260842
    assert len(audit['source_proofs']) == 110 and len(audit['large_binary_cases']) == 10
    assert audit['sphere_boundary_betti'] == {'2': [1, 1, 1, 0], '3': [1, 0, 0, 0]}
    assert audit['pilot_sha256'] == sha256((DATA/'complement-chamber-pilot.json').read_bytes()).hexdigest()
    assert audit['corpus_sha256'] == sha256((ROOT/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest()
    # The audit never executes the benchmark driver. Its original source
    # snapshot is retained; only the driver switched from canonical IsoSig
    # to reversible labelled encoding after the audit completed.
    historical = []
    for path, digest in audit['native_source_sha256'].items():
        if sha256((ROOT/path).read_bytes()).hexdigest() != digest:
            assert path == 'fast/benchmark_cut_cells.py', path
            blob = subprocess.check_output(['git', 'show', audit['source_snapshot_revision']+':Topology/UnknotRecognition/'+path], cwd=REPO)
            assert sha256(blob).hexdigest() == digest, path
            historical.append(path)
    for path, digest in benchmark['source_sha256'].items(): assert sha256((REPO/path).read_bytes()).hexdigest() == digest, path
    assert re.search(r'Ran 1599 tests in [0-9.]+s\n\nOK\n', (DATA/'cut-cells-tests.txt').read_text())
    assert re.search(r'Ran 10 tests in [0-9.]+s\n\nOK\n', (DATA/'cut-cells-focused.txt').read_text())
    disabled = ('fastunknot.normal_cut_cells._cut_cells', 'fastunknot.normal_cut_cells._orientations',
                'fastunknot.normal_cut_cells._summary', 'fastunknot.normal_cut_cells.normal_cut_cell_complex',
                'fastunknot.normal_cut_boundary._cycle_recipes', 'fastunknot.normal_cut_boundary._boundary_system',
                'fastunknot.normal_cut_complement._chamber_system', 'fastunknot.interval_orbits.count_orbits')
    with ExitStack() as stack:
        for name in disabled: stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
        for row in audit['source_proofs']:
            assert verify_normal_cut_cell_complex(row['triangulation'], row['coordinates'], row['certificate']), row['id']
            g = row['certificate']['geometry']; t = len(row['coordinates'])
            assert len(g['vertices']) <= 16*t and len(g['edges']) <= 30*t and len(g['faces']) <= 26*t and len(g['chambers']) <= 5*t
            assert sum(len(e['incidences']) for e in g['edges']) <= 180*t and len(g['face_incidence']) <= 56*t
    assert len(benchmark['samples']) == 126
    for name, summary in benchmark['summary'].items():
        rows = [r for r in benchmark['samples'] if r['case'] == name]
        assert len(rows) == 18 and all(r['completed'] for r in rows)
        assert len({r['euler_characteristic'] for r in rows}) == 1
        for arm in ('regina', 'regina_control', 'native'):
            selected = [r for r in rows if r['arm'] == arm]
            assert sorted(r['round'] for r in selected) == list(range(6))
            assert all(r['warmup'] == (r['round'] == 0) and r['seconds'] > 0 for r in selected)
            assert summary['median_seconds'][arm] == statistics.median(r['seconds'] for r in selected if not r['warmup'])
        def paired(other):
            return statistics.median(next(r['seconds'] for r in rows if r['arm'] == 'regina' and r['round'] == i)/
                                     next(r['seconds'] for r in rows if r['arm'] == other and r['round'] == i) for i in range(1, 6))
        assert summary['paired_regina_over_native'] == paired('native') and summary['identical_control'] == paired('regina_control')
    result = dict(source_snapshot_pins=len(audit['native_source_sha256']), source_snapshot_revision=audit['source_snapshot_revision'],
        historical_nonoperation_pins=historical, maintained_tests=1599, maintained_skips=0, focused_tests=10,
        finite_cuts=1755, integral_zero_checks=233036, edge_face_incidences=638563, face_chamber_incidences=260842,
        producer_disabled_proofs=110, binary_cases=10, measured_samples=105, warmup_samples=21,
        full_raw_interior_cells=True, parallelity_removed=False, bounded_admissible_core=False, general_quasipolynomial_recognition=False)
    if args.publication:
        log = (ROOT/'synthesis/report.log').read_text()
        assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error', log)
        warnings = re.findall(r'Overfull \\hbox \(([^)]*)\)', log)
        assert warnings == [f'{x}pt too wide' for x in ('12.64871', '13.49065', '9.04614', '35.14671')], warnings
        aux = (ROOT/'synthesis/report.aux').read_text(); toc = (ROOT/'synthesis/report.toc').read_text()
        first = int(re.search(r'\\newlabel\{sec:cut-cells\}\{\{162\}\{(\d+)\}', aux).group(1))
        assessment = int(re.search(r'\\numberline \{163\}Assessment and recommendations\}\{(\d+)\}', toc).group(1))
        visual = read('cut-cells-visual-review.json')
        assert visual['pdf_sha256'] == sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
        assert visual['inspected_pages'] == list(range(first, assessment+3))
        result.update(pdf_pages=int(re.search(r'Output written on report.pdf \((\d+) pages,', log).group(1)),
                      section_page=first, assessment_page=assessment, visual_review=visual, preexisting_overfull_warnings=warnings)
    paths = [Path(__file__), DATA/'cut_cells_tables.py', DATA/'cut-cells-audit.json', DATA/'cut-cells-benchmark.json',
             DATA/'cut-cells-tests.txt', DATA/'cut-cells-focused.txt', ROOT/'synthesis/cut_cells.tex', ROOT/'synthesis/tables/cut_cells.tex',
             ROOT/'synthesis/make_tables.py', ROOT/'synthesis/report.tex', ROOT/'synthesis/report.pdf', ROOT/'README.md', ROOT/'fast/README.md', ROOT/'synthesis/README.md']
    result['evidence_sha256'] = {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest() for p in paths}
    name = 'cut-cells-publication-review.json' if args.publication else 'cut-cells-runtime-review.json'
    (DATA/name).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('evidence_sha256','visual_review')}, indent=2))


if __name__ == '__main__': main()
