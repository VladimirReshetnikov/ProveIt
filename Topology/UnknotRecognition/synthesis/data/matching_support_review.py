"""Review source-equation forcing, independent linear replay and publication."""
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
from fastunknot.normal_sector_verify import verify_sector_exhaustion

def read(name):return json.loads((DATA/name).read_text())
def frozen(revision,pins,current=False):
    prefix='Topology/UnknotRecognition/'
    raw=subprocess.check_output(['git','archive',revision]+[prefix+p for p in pins],cwd=ROOT.parents[1])
    with tarfile.open(fileobj=BytesIO(raw))as archive:
        for p,h in pins.items():
            assert sha256(archive.extractfile(prefix+p).read()).hexdigest()==h,p
            if current:assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p

audit=read('matching-support-audit.json');bench=read('matching-support-benchmark.json')
pins=audit['native_source_sha256'];assert pins==bench['native_source_sha256']
frozen(audit['native_runtime_revision'],pins,True)
prior=read('feasible-span-audit.json');frozen(prior['native_runtime_revision'],prior['native_source_sha256'])
assert audit['source_sectors']==audit['unchanged_statuses']==len(audit['source_cases'])==188
assert audit['forced_zero_sectors']==sum(r['forced_zero_types']>0 for r in audit['source_cases'])==65
assert audit['dimension_transitions']=={'4->3':22,'4->4':41,'5->4':2}
assert audit['fresh_regina_sources']==3
assert sum('matching_support_reduction'in r['new_stats']for r in audit['source_cases'])==65
assert sum(r['forced_zero_types']for r in audit['source_cases'])==126
for r in audit['source_cases']:
    if r['raw_nullity']==4 and r['feasible_nullity']==3:
        assert 'q_screen_stats'not in r['new_stats'] and r['new_stats']['method']=='planar-adaptive'
assert all(r['old_status']==r['new_status']for r in audit['source_cases'])
assert all(r['fresh_regina_standard_rays']==r['standard_rays']for r in audit['source_cases']if r['forced_zero_types'])
for r in audit['source_cases']:
    proof=r['certificate']
    assert proof['allowed_types']==r['allowed_types']
    if 'matching_support_certificate'in proof:
        assert r['new_stats']['matching_support_reduction']['retained_indices']==r['retained_indices']
        assert proof['matching_support_certificate']['allowed_types']==r['allowed_types']
        assert all(len(entry['quadrilaterals'])==len(r['allowed_types'])for entry in proof['rays'])
assert {r['legacy_dimension']for r in audit['source_cases']if 'legacy_dimension'in r}=={3,4}
disabled=('fastunknot.normal_sector.build_sector_kernel','fastunknot.normal_sector.sector_rays',
    'fastunknot.normal_sector._discover_in_kernel','fastunknot.sector_euler._q_corner_parameters',
    'fastunknot.sector_matching_support.matching_support','fastunknot.sector_matching_support._source_constraints',
    'fastunknot.sector_planar.sector_planar_rays','fastunknot.sector_euler.SourceEuler.__init__',
    'fastunknot.normal_seed.normal_seed_decide','fastunknot.normal_disk_kernel.normal_compressing_disk_count')
saved=(DATA/'generic-euler-audit.json').read_bytes()
assert saved==subprocess.check_output(['git','show',audit['native_baseline']+':Topology/UnknotRecognition/synthesis/data/generic-euler-audit.json'],cwd=ROOT)
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer invoked during replay')))
    for record in audit['reduced_proofs']:
        assert verify_sector_exhaustion(record['triangulation'],record['certificate'])
    changed=deepcopy(audit['reduced_proofs'][0]);changed['certificate']['matching_support_certificate']['steps'][0]['forced_indices'].pop()
    assert not verify_sector_exhaustion(changed['triangulation'],changed['certificate'])
    for proof in read('generic-euler-audit.json')['source_proofs']:
        assert verify_normal_seed_certificate(Diagram.from_pd(proof['input_pd']),proof)
assert bench['measured_calls']==bench['completed_calls']==100 and bench['warmup_calls']==20
for row in bench['cases']:
    samples=row['samples']+row['warmups']
    statuses={v['status']for sample in samples for v in sample['measurements'].values()}
    assert len(statuses)==1
    for arm in ('old','old_AA','new','new_AA'):
        assert all(sample['measurements'][arm]['completed']for sample in samples)
        assert len({sample['measurements'][arm]['certificate_sha256']for sample in samples})==1
assert re.search(r'Ran 1433 tests in [0-9.]+s\n\nOK', (DATA/'matching-support-tests.txt').read_text())
assert re.search(r'Ran 34 tests in [0-9.]+s\n\nOK', (DATA/'matching-support-focused.txt').read_text())
result=dict(runtime_revision=audit['native_runtime_revision'],source_pins=len(pins),
    incumbent_evidence_pins=len(prior['native_source_sha256']),maintained_tests=1433,focused_tests=34,
    source_sectors=188,forced_zero_sectors=65,dimension_transitions=audit['dimension_transitions'],
    fresh_regina_sources=3,producer_disabled_reduced_proofs=len(audit['reduced_proofs']),
    producer_disabled_saved_diagram_proofs=len(read('generic-euler-audit.json')['source_proofs']),
    complete_measured_calls=100,warmups=20)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
    start=int(re.search(r'\\newlabel\{sec:matching-support\}\{\{147\}\{(\d+)\}',(ROOT/'synthesis/report.aux').read_text()).group(1))
    end=int(re.search(r'\\numberline \{148\}Assessment and recommendations\}\{(\d+)\}',(ROOT/'synthesis/report.toc').read_text()).group(1))
    visual=read('matching-support-visual-review.json')
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,end+3))
    result.update(pdf_pages=pages,new_section_start=start,assessment_page=end,
        preexisting_overfull_warnings=warnings,visual_review=visual)
    (DATA/'matching-support-latex.txt').write_text('\n'.join(line.rstrip()for line in log.splitlines()).rstrip()+'\n')
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/matching_support.tex','synthesis/matching_support_results.tex',
        'synthesis/data/matching_support_review.py','synthesis/data/matching_support_tables.py',
        'fast/README.md','synthesis/README.md','synthesis/feasible_span.tex',
        'synthesis/make_tables.py','synthesis/tables/matching_support_queries.tex']
    result['publication_sha256']={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths}
(DATA/('matching-support-review.json'if '--publication'in sys.argv else 'matching-support-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('publication_sha256','visual_review')}))
