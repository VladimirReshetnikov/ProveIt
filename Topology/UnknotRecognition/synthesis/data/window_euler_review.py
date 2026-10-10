"""Verify source Euler screening, prepared observers and independent publication."""
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
def frozen(revision,pins,current=False):
    prefix='Topology/UnknotRecognition/'
    raw=subprocess.check_output(['git','archive',revision]+[prefix+p for p in pins],cwd=ROOT.parents[1])
    with tarfile.open(fileobj=BytesIO(raw))as archive:
        for p,h in pins.items():
            assert sha256(archive.extractfile(prefix+p).read()).hexdigest()==h,p
            if current:assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p

audit=read('window-euler-audit.json');bench=read('window-euler-benchmark.json');pilot=read('window-euler-pilot.json');repeat=read('window-euler-repeat.json')
pins=audit['native_source_sha256'];assert len(pins)==598
assert pins==bench['native_source_sha256']==repeat['native_source_sha256']
frozen('f95a86fdf',pins,True)
prior=read('window-basis-audit.json');frozen('b1741c008',prior['native_source_sha256'])
for name,h in audit['native_baseline_source_sha256'].items():
    code=subprocess.check_output(['git','show',audit['native_baseline']+':Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'],cwd=ROOT)
    assert sha256(code).hexdigest()==h==bench['native_baseline_source_sha256'][name]==repeat['native_baseline_source_sha256'][name]
changes=subprocess.check_output(['git','diff','--name-only',audit['native_baseline'],'f95a86fdf','--','Topology/UnknotRecognition/fast'],cwd=ROOT.parents[1]).decode().splitlines()
assert set(changes)=={'Topology/UnknotRecognition/'+p for p in ('fast/fastunknot/sector_residual.py',
    'fast/fastunknot/sector_window_basis.py','fast/fastunknot/sector_euler.py','fast/fastunknot/normal_disk_kernel.py','fast/normal_orbit_research/window_euler.py','fast/tests/test_sector_euler.py')}
assert audit['legacy_exact_comparisons']==85
assert audit['old_radius_two_positives']==31 and audit['new_radius_two_positives']>=31
assert audit['fresh_regina_window_discs']==sum(p['schema']=='diagram-normal-disc-v1'for p in audit['source_proofs'])
assert len(audit['source_cases'])==85
assert all(r['new_radius_two_status']=='UNKNOT'for r in audit['source_cases']if r['old_radius_two_status']=='UNKNOT')
caps=sum('exhausted'in (r['reason']or'')for r in audit['source_cases'])
misses=sum(bool(r['new_window_stats']and r['new_window_stats']['window_complete'])for r in audit['source_cases'])
assert all(s['full_basis_builds']==1 for r in audit['source_cases']if (s:=r['new_window_stats'])and s['basis_updates'])
disabled=['fastunknot.sector_euler.SourceEuler.__init__','fastunknot.sector_euler.SourceEuler.excludes_positive',
    'fastunknot.sector_euler.SourceEuler.canonical_value','fastunknot.sector_window_basis.projected_corner_forms',
    'fastunknot.normal_disk_kernel._count_prepared_discs','fastunknot.sector_residual._count_prepared_discs',
    'fastunknot.sector_window_basis.WindowBasis.for_edits',
    'fastunknot.sector_window_basis.canonical_matching_basis','fastunknot.sector_window_basis.projected_window_kernel',
    'fastunknot.sector_residual._plan_window','fastunknot.sector_residual._full_quad_columns',
    'fastunknot.sector_residual.search_sector_window','fastunknot.normal_seed.normal_seed_decide',
    'fastunknot.normal_cocycle._rank_one_cocycle_seed_details','fastunknot.cocycle_span.minimize_cocycle_span',
    'fastunknot.normal_sector.build_sector_kernel','fastunknot.normal_sector.sector_rays',
    'fastunknot.normal_disk_kernel.normal_compressing_disk_count','fastunknot.normal_disk_kernel.canonical_disk_core',
    'fastunknot.interval_orbits.count_orbits','fastunknot.interval_orbits._count_orbits',
    'fastunknot.diagram_exterior.diagram_exterior']
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer called during replay')))
    for proof in audit['source_proofs']:
        assert verify_normal_seed_certificate(Diagram.from_pd(proof['input_pd']),proof)
assert len(audit['source_proofs'])==audit['new_radius_two_positives']
for record,calls,warm in ((bench,200,40),(pilot,120,40),(repeat,60,4)):
    assert record['completed_calls']==record['measured_calls']==calls and record['warmup_calls']==warm
    for row in record['cases']:
        values=[v for s in row['samples']+row['warmups']for v in s['measurements'].values()]
        assert all(v['completed']and v['status']==values[0]['status']for v in values)
        if row['name'].startswith('seed/'):
            assert all(v['certificate_sha256']==values[0]['certificate_sha256']for v in values)
assert 'Ran 1407 tests in 240.354s\n\nOK' in (DATA/'window-euler-tests.txt').read_text()
assert 'Ran 15 tests in 18.920s\n\nOK' in (DATA/'window-euler-focused.txt').read_text()
for p,h in pilot['native_source_sha256'].items():
    path=DATA/'window-euler-pilot-source'/p
    if not path.exists():path=ROOT/p
    assert sha256(path.read_bytes()).hexdigest()==h,p
assert len(pilot['native_source_sha256'])==598
assert sha256((DATA/'window_euler_repeat.py').read_bytes()).hexdigest()==repeat['driver_sha256']
result=dict(runtime_revision='f95a86fdf',source_pins=598,incumbent_evidence_pins=595,
    maintained_tests=1407,focused_tests=15,exact_disabled_cases=85,
    unchanged_enabled_verdicts=sum(r['old_radius_two_status']==r['new_radius_two_status']for r in audit['source_cases']),
    preserved_native_positives=audit['new_radius_two_positives'],fresh_regina_window_discs=audit['fresh_regina_window_discs'],
    work_caps=caps,completed_window_misses=misses,
    producer_disabled_positive_replays=len(audit['source_proofs']),measured_calls=200,warmups=40,
    exploratory_euler_only_measured_calls=120,exploratory_euler_only_warmups=40,noisy_native_repeat_measured_calls=60,noisy_native_repeat_warmups=4)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
    start=int(re.search(r'\\newlabel\{sec:window-euler\}\{\{140\}\{(\d+)\}',(ROOT/'synthesis/report.aux').read_text()).group(1))
    end=int(re.search(r'\\numberline \{141\}Assessment and recommendations\}\{(\d+)\}',(ROOT/'synthesis/report.toc').read_text()).group(1))
    visual=read('window-euler-visual-review.json')
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,end+2))
    result.update(pdf_pages=pages,new_section_start=start,assessment_page=end,
        preexisting_overfull_warnings=warnings,visual_review=visual)
    (DATA/'window-euler-latex.txt').write_text('\n'.join(line.rstrip()for line in log.splitlines()).rstrip()+'\n')
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/window_euler.tex','synthesis/window_euler_results.tex',
        'synthesis/data/window_euler_review.py','synthesis/data/window_euler_tables.py','synthesis/data/window_euler_repeat.py',
        'fast/README.md','synthesis/README.md']
    result['publication_sha256']={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths}
(DATA/('window-euler-review.json'if '--publication'in sys.argv else 'window-euler-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('publication_sha256','visual_review')}))
