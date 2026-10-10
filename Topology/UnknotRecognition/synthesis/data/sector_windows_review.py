"""Check source pins, added native discs and final manuscript publication."""
from contextlib import ExitStack
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[2];DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot import Diagram
from fastunknot.normal_seed_verify import verify_normal_seed_certificate

def read(name):return json.loads((DATA/name).read_text())

audit=read('sector-windows-audit.json');bench=read('sector-windows-benchmark.json');repeat=read('sector-windows-repeat.json')
pins=audit['native_source_sha256'];assert len(pins)==592
assert pins==bench['native_source_sha256']==repeat['native_source_sha256']
prefix='Topology/UnknotRecognition/'
raw=subprocess.check_output(['git','archive','a498521ef']+[prefix+p for p in pins],cwd=ROOT.parents[1])
with tarfile.open(fileobj=BytesIO(raw))as archive:
    for p,h in pins.items():
        assert sha256(archive.extractfile(prefix+p).read()).hexdigest()==h,p
        assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
baseline=subprocess.check_output(['git','show',audit['native_baseline']+':'+prefix+'fast/fastunknot/normal_seed.py'],cwd=ROOT)
assert sha256(baseline).hexdigest()==audit['native_baseline_source_sha256']==bench['native_baseline_source_sha256']
assert audit['legacy_exact_comparisons']==85 and audit['old_positives']==24 and audit['new_positives']==31
assert len(audit['added_positive_proofs'])==audit['fresh_regina_added_discs']==7
added=[r for r in audit['source_cases']if r['added_positive']]
assert len({str(r['certificate']['input_pd'])for r in added})==6
assert sum('exhausted'in (r['reason']or'')for r in audit['source_cases'])==34
assert sum(bool(r['window_stats']and r['window_stats']['window_complete'])for r in audit['source_cases'])==20
disabled=['fastunknot.sector_residual.plan_sector_window','fastunknot.sector_residual._plan_window',
    'fastunknot.sector_residual._full_quad_columns','fastunknot.sector_residual.search_sector_window',
    'fastunknot.normal_seed.normal_seed_decide','fastunknot.normal_cocycle.rank_one_cocycle_seed',
    'fastunknot.normal_cocycle._rank_one_cocycle_seed_details','fastunknot.cocycle_span.minimize_cocycle_span',
    'fastunknot.normal_sector.build_sector_kernel','fastunknot.normal_sector.sector_rays',
    'fastunknot.normal_disk_kernel.normal_compressing_disk_count','fastunknot.normal_disk_kernel.canonical_disk_core',
    'fastunknot.interval_orbits.count_orbits','fastunknot.interval_orbits._count_orbits',
    'fastunknot.diagram_exterior.diagram_exterior']
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer called during replay')))
    for proof in audit['source_proofs']:
        assert verify_normal_seed_certificate(Diagram.from_pd(proof['input_pd']),proof)
assert len(audit['source_proofs'])==31
for record,calls,warm in ((bench,200,40),(repeat,180,12)):
    assert record['completed_calls']==record['measured_calls']==calls and record['warmup_calls']==warm
    assert all(v['completed']for row in record['cases']for s in row['samples']+row['warmups']for v in s['measurements'].values())
assert 'Ran 1401 tests in 234.317s\n\nOK' in (DATA/'sector-windows-tests.txt').read_text()
assert 'Ran 26 tests in 4.368s\n\nOK' in (DATA/'sector-windows-focused.txt').read_text()
neighbours=read('sector-windows-exploratory-seed-sector-neighbours.json')
assert sum(len(r['records'])for r in neighbours)==2340
assert all(q['status']in ('NO_POSITIVE_EULER','NO_VERTEX_DISC_IN_SECTOR')for r in neighbours for q in r['records'])
unfiltered=read('sector-windows-exploratory-radius-two.json');filtered=read('sector-windows-exploratory-residual-probe.json')
assert len(unfiltered['records'])==4920 and filtered['queries']==31
for proof in (unfiltered['proof'],filtered['proof']):
    assert verify_normal_seed_certificate(Diagram.from_pd(proof['input_pd']),proof)
result=dict(runtime_revision='a498521ef',source_pins=592,maintained_tests=1401,focused_tests=26,
    exact_disabled_cases=85,old_native_positives=24,new_native_positives=31,added_source_cases=7,
    distinct_added_canonical_PD_codes=6,fresh_regina_added_disc_checks=7,work_capped_cases=34,
    completed_window_misses=20,producer_disabled_positive_replays=31,
    radius_one_exploratory_queries=2340,unfiltered_successful_prefix_queries=4920,filtered_successful_prefix_queries=31,
    measured_calls=200,warmups=40,noisy_repeat_measured_calls=180,noisy_repeat_warmups=12)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
    start=int(re.search(r'\\newlabel\{sec:sector-windows\}\{\{138\}\{(\d+)\}',(ROOT/'synthesis/report.aux').read_text()).group(1))
    end=int(re.search(r'\\numberline \{139\}Assessment and recommendations\}\{(\d+)\}',(ROOT/'synthesis/report.toc').read_text()).group(1))
    visual=read('sector-windows-visual-review.json')
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,end+2))
    result.update(pdf_pages=pages,new_section_start=start,assessment_page=end,
        preexisting_overfull_warnings=warnings,visual_review=visual)
    (DATA/'sector-windows-latex.txt').write_text('\n'.join(line.rstrip()for line in log.splitlines()).rstrip()+'\n')
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/sector_windows.tex','synthesis/sector_windows_results.tex',
        'synthesis/data/sector_windows_review.py','synthesis/data/sector_windows_tables.py','synthesis/data/sector_windows_repeat.py',
        'fast/README.md','synthesis/README.md']
    result['publication_sha256']={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths}
(DATA/('sector-windows-review.json'if '--publication'in sys.argv else 'sector-windows-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('publication_sha256','visual_review')}))
