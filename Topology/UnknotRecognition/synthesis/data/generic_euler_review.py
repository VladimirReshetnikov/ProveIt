"""Review generic Q screens, independent sector proofs and published evidence."""
from contextlib import ExitStack
from copy import deepcopy
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
from fastunknot.normal_disk_kernel import _DiskCertificateVerifier,verify_normal_disk_count_certificate
from fastunknot.normal_sector_verify import verify_sector_exhaustion

def read(name):return json.loads((DATA/name).read_text())
def frozen(revision,pins,current=False):
    prefix='Topology/UnknotRecognition/'
    raw=subprocess.check_output(['git','archive',revision]+[prefix+p for p in pins],cwd=ROOT.parents[1])
    with tarfile.open(fileobj=BytesIO(raw))as archive:
        for p,h in pins.items():
            assert sha256(archive.extractfile(prefix+p).read()).hexdigest()==h,p
            if current:assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p

audit=read('generic-euler-audit.json');sectors=read('generic-euler-sector-audit.json')
bench=read('generic-euler-benchmark.json');sector_bench=read('generic-euler-sector-benchmark.json')
pins=audit['native_source_sha256'];revision=audit['native_runtime_revision']
assert pins==sectors['native_source_sha256']==bench['native_source_sha256']==sector_bench['native_source_sha256']
frozen(revision,pins,True)
prior=read('euler-aggregate-audit.json');frozen('71e1e5225',prior['native_source_sha256'])
assert audit['legacy_exact_comparisons']==85 and len(audit['source_cases'])==85
assert audit['old_radius_two_positives']==31 and audit['new_radius_two_positives']>=31
assert all(r['new_radius_two_status']==r['old_radius_two_status']for r in audit['source_cases'])
assert sectors['source_sectors']==len(sectors['sector_cases'])==188
assert sectors['matching_nullities']==[4,5]
assert sum(c['matching_nullity']==4 for c in sectors['sector_cases'])==177
assert sum(c['matching_nullity']==5 for c in sectors['sector_cases'])==11
excluded=[c for c in sectors['sector_cases']if c['excluded']]
assert sectors['excluded_sectors']==len(excluded)==12
assert all(c['q_corners']==4 and c['standard_rays']==15 for c in excluded)
assert len(sectors['negative_proofs'])==12 and sectors['fresh_regina_sources']==4
assert all(c['fresh_regina_standard_rays']==15 for c in excluded)
for c in sectors['sector_cases']:
    assert c['excluded']==(not any(x>0 for x in c['q_euler']))==(not any(x>0 for x in c['standard_euler']))
    if c['excluded']:assert c['screen_stats']['euler_corners']==c['q_corners']
disabled=['fastunknot.sector_euler.SourceEuler.aggregate','fastunknot.sector_euler.SourceEuler.aggregated_value',
    'fastunknot.normal_disk_kernel._DiskCertificateVerifier.__init__',
    'fastunknot.normal_disk_kernel._DiskCertificateVerifier.verify','fastunknot.normal_disk_kernel._DiskCertificateVerifier._homology_basis',
    'fastunknot.sector_linear_form.SparseLinearForm.dot','fastunknot.sector_linear_form.SparseLinearForm.project',
    'fastunknot.sector_window_basis.WindowBasis.project_modes',
    'fastunknot.sector_window_basis.WindowBasis._corrected_column','fastunknot.sector_euler.SourceEuler.__init__','fastunknot.sector_euler.SourceEuler.excludes_positive',
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
disabled += ['fastunknot.sector_euler._q_corner_parameters','fastunknot.normal_sector._discover_in_kernel']
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer called during replay')))
    for row in sectors['negative_proofs']:
        assert verify_sector_exhaustion(row['triangulation'],row['certificate'])
    altered=deepcopy(sectors['negative_proofs'][0]);altered['certificate']['rays'].pop()
    assert not verify_sector_exhaustion(altered['triangulation'],altered['certificate'])
    for proof in audit['source_proofs']:
        assert verify_normal_seed_certificate(Diagram.from_pd(proof['input_pd']),proof)
generic=read('disc-context-generic-replay.json')
assert generic['status']=='PASS'and len(generic['records'])==8
with ExitStack()as stack:
    for name in disabled:
        if '_DiskCertificateVerifier.'not in name:
            stack.enter_context(patch(name,side_effect=AssertionError('producer called during generic replay')))
    verifier=_DiskCertificateVerifier(generic['triangulation'])
    for r in generic['records']:
        assert r['certificate']['schema']=='normal-disc-count-v1'
        assert verify_normal_disk_count_certificate(generic['triangulation'],r['coordinates'],r['certificate'])
        assert verifier.verify(generic['triangulation'],r['coordinates'],r['certificate'])
for record,calls,warm in ((bench,200,40),(sector_bench,120,24)):
    assert record['completed_calls']==record['measured_calls']==calls and record['warmup_calls']==warm
    for row in record['cases']:
        values=[v for s in row['samples']+row['warmups']for v in s['measurements'].values()]
        assert all(v['completed']and v['status']==values[0]['status']for v in values)
        for arm in ('old','old_AA','new','new_AA'):
            hashes={sample['measurements'][arm].get('certificate_sha256')for sample in row['samples']+row['warmups']}
            assert len(hashes)==1
assert re.search(r'Ran 1422 tests in [0-9.]+s\n\nOK', (DATA/'generic-euler-tests.txt').read_text())
assert re.search(r'Ran 23 tests in [0-9.]+s\n\nOK', (DATA/'generic-euler-focused.txt').read_text())
caps=sum('exhausted'in (r['reason']or'')for r in audit['source_cases'])
misses=sum(bool(r['new_window_stats']and r['new_window_stats']['window_complete'])for r in audit['source_cases'])
result=dict(runtime_revision=revision,source_pins=len(pins),incumbent_evidence_pins=len(prior['native_source_sha256']),
    maintained_tests=1422,focused_tests=23,exact_disabled_cases=85,unchanged_enabled_verdicts=85,
    preserved_native_positives=audit['new_radius_two_positives'],fresh_regina_window_discs=audit['fresh_regina_window_discs'],
    work_caps=caps,completed_window_misses=misses,source_sectors=188,excluded_sectors=12,
    fresh_regina_sector_sources=4,producer_disabled_negative_replays=12,
    producer_disabled_positive_replays=len(audit['source_proofs']),generic_v1_replays=8,
    diagram_measured_calls=200,diagram_warmups=40,sector_measured_calls=120,sector_warmups=24)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
    start=int(re.search(r'\\newlabel\{sec:generic-euler\}\{\{145\}\{(\d+)\}',(ROOT/'synthesis/report.aux').read_text()).group(1))
    end=int(re.search(r'\\numberline \{146\}Assessment and recommendations\}\{(\d+)\}',(ROOT/'synthesis/report.toc').read_text()).group(1))
    visual=read('generic-euler-visual-review.json')
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,end+3))
    result.update(pdf_pages=pages,new_section_start=start,assessment_page=end,
        preexisting_overfull_warnings=warnings,visual_review=visual)
    (DATA/'generic-euler-latex.txt').write_text('\n'.join(line.rstrip()for line in log.splitlines()).rstrip()+'\n')
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/generic_euler.tex','synthesis/generic_euler_results.tex',
        'synthesis/data/generic_euler_review.py','synthesis/data/generic_euler_tables.py',
        'fast/README.md','synthesis/README.md']
    result['publication_sha256']={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths}
(DATA/('generic-euler-review.json'if '--publication'in sys.argv else 'generic-euler-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('publication_sha256','visual_review')}))
