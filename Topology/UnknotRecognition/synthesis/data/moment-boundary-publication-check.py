"""Validate the frozen native moment integration and publication evidence."""
import hashlib
import json
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[2]
DATA = Path(__file__).parent
sys.path.insert(0, str(ROOT / 'fast'))
from normal_orbit_research.seeds import sources

sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((DATA / (n + '.json')).read_text())
a = read('moment-boundary-audit')
b = read('moment-boundary-benchmark')
assert a['native_source_sha256'] == b['native_source_sha256'] == sources()
assert a['corpus_sha256'] == b['corpus_sha256'] == sha(ROOT / 'fast/marked_parallelity_research/corpus.json')
assert a['fixture_sha256'] == sha(ROOT / 'fast/marked_parallelity_research/three_handle_corpus.json')
assert b['moment_corpus_sha256'] == sha(ROOT / 'fast/marked_parallelity_research/moment_corpus.json')
assert b['driver_sha256'] == sha(DATA / 'moment-boundary-benchmark.py')
assert all(sha(DATA / n) == h for n, h in a['reference_sha256'].items())
assert all(sha(DATA / 'moment-boundary-baseline' / n) == h for n, h in b['baseline_sha256'].items())
assert len(a['cases']) == 120 and a['complete'] == 102
assert a['earlier_masks_unchanged'] == 92 and a['literal_agreements'] == 95
old = {r['id']: r for r in read('three-handles-audit')['cases'] if r['native_status'] == 'COMPLETE'}
new = {r['id']: r for r in a['cases'] if r['status'] == 'COMPLETE'}
assert len(new) == 102
assert sum(r['literal_reference'] for r in new.values()) == 95
assert all(new[k]['masks_sha256'] == r['certificate_sha256'] for k, r in old.items())
assert b['finished'] and b['rounds'] == 5 and len(b['cases']) == 7
for r in b['cases']:
    assert len(r['samples']) == 5 and len(r['aa_samples']) == 3
    for method in ('masks', 'moments'):
        assert r[method + '_median'] == statistics.median(s[method]['total'] for s in r['samples'])
    assert r['paired_speedup'] == statistics.median(s['masks']['total'] / s['moments']['total'] for s in r['samples'])
    assert r['aa_median'] == statistics.median(s['ratio'] for s in r['aa_samples'])
    assert 0 < r['moments_certificate_bytes'] < r['masks_certificate_bytes']
    if r['ports']:
        assert r['moments_boundary_stats']['compilation']['weighted_calls'] == 1
        assert r['moments_boundary_stats']['compilation']['terminal_labels'] == 4 * r['ports']
        assert r['moments_boundary_stats']['census']['orbit_cycles'] == r['masks_boundary_stats']['gap_cover']['orbit_cycles']
    else:
        assert r['moments_boundary_stats'] == r['masks_boundary_stats'] == {}
assert sum(r['paired_speedup'] > 1 for r in b['cases']) == 5
binary = read('moment-boundary-delivered-native_moments_binary')
coverage = read('moment-boundary-delivered-native_moments_coverage')
assert coverage == dict(cap_only=5, loop_edges=0, positive_gaps=219,
                        point_gaps=3420, circle_attachments=181,
                        fibre_flips=546, literal_cases=146)
assert [r['bits'] for r in binary] == [32, 512, 16384]
assert all(r['cycles'] == 131 and r['owner_intervals'] == 60 and r['weight_records'] == 68 for r in binary)
for name, count, seconds in [('focused', 9, '164.451'), ('whole-focused', 5, '6.662'),
                             ('delivered-tests', 9, '159.509')]:
    log = (DATA / ('moment-boundary-' + name + '.txt')).read_text()
    assert f'Ran {count} tests in {seconds}s\n\nOK' in log
log = (DATA / 'moment-boundary-tests.txt').read_text()
assert 'Ran 1710 tests in ' in log and '\n\nOK\n' in log and 'skipped=' not in log
artifacts = sorted(p for p in DATA.glob('moment-boundary-*')
                   if p.is_file() and p != Path(__file__).with_suffix('.json'))
report = dict(scope='One-query source-bound supplied-cut boundary; no global recognition bound',
              native_source_pins_match=True, delivered_tests=9, native_focused_tests=14,
              full_tests=1710, source_cases=120, complete_cuts=102,
              earlier_mask_certificates_unchanged=92, retained_literal_agreements=95,
              benchmark_cases=7, cases_with_paired_gain=5,
              artifact_sha256={p.name: sha(p) for p in artifacts},
              report_pdf_sha256=sha(ROOT / 'synthesis/report.pdf'))
Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2) + '\n')
print('Publication checks pass: 102 cuts, 92 unchanged mask certificates, 1710 tests.')
