"""Review moved-source primitive annulus caps and original input authority."""
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
from fastunknot.normal_transport_verify import verify_transport_disk_certificate,verify_transport_annulus_certificate

def read(name):return json.loads((DATA/name).read_text())
def frozen(revision,pins,current=False):
    prefix='Topology/UnknotRecognition/'
    raw=subprocess.check_output(['git','archive',revision]+[prefix+p for p in pins],cwd=ROOT.parents[1])
    with tarfile.open(fileobj=BytesIO(raw))as archive:
        for p,h in pins.items():
            assert sha256(archive.extractfile(prefix+p).read()).hexdigest()==h,p
            if current:assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p

audit=read('transport-annulus-audit.json');bench=read('transport-annulus-benchmark.json')
pins=audit['native_source_sha256'];assert pins==bench['native_source_sha256']
frozen(audit['native_runtime_revision'],pins,True)
assert audit['disabled_exact_cases']==len(audit['diagram_cases'])==6
assert len(audit['fresh_regina_checks'])==len(audit['diagram_proofs'])
assert re.search(r'Ran 1529 tests in [0-9.]+s\n\nOK',(DATA/'transport-annulus-tests.txt').read_text())
assert re.search(r'Ran 36 tests in [0-9.]+s\n\nOK',(DATA/'transport-annulus-focused.txt').read_text())
case=next(r for r in audit['diagram_cases']if r['source']['name']=='optimized-positive')
assert case['old_status']=='INCONCLUSIVE'and case['new_status']=='UNKNOT'
assert case['enabled_positive_method']=='native-pachner-annulus'
assert case['new_stats']['epochs']==0 and case['new_stats']['annulus_queries']==1
assert case['certificate']['schema']=='diagram-transport-annulus-v1'
for r in audit['diagram_cases']:
    assert r['disabled_status']==r['enabled_capped_status']==r['source']['expected']
    assert all(e['after']<e['before']and e['upward_moves']<=1 for e in r['new_stats']['epoch_records'])
    assert r['new_stats']['nodes']<=1000
disabled=('fastunknot.pachner_epochs.pachner_epoch_seed_decide','fastunknot.pachner_epochs.find_pachner_descent',
    'fastunknot.pachner_cover_search.find_pachner_descent','fastunknot.pachner_cover_search.search_pachner_cover',
    'fastunknot.pachner23.pachner_23','fastunknot.pachner32.pachner_32',
    'fastunknot.cocycle_transport.transport_cocycle','fastunknot.cocycle_transport.descend_cocycle',
    'fastunknot.cocycle_gauge.optimize_cocycle_gauge','fastunknot.cocycle_span.minimize_cocycle_span',
    'fastunknot.diagram_exterior.diagram_exterior','fastunknot.normal_disk_kernel.normal_compressing_disk_count')
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used during full-chain replay')))
    for proof in audit['diagram_proofs']:
        assert (verify_transport_annulus_certificate if proof['schema']=='diagram-transport-annulus-v1'else verify_transport_disk_certificate)(Diagram.from_pd(proof['input_pd']),proof)
    wrong=deepcopy(case['certificate']);wrong['surface_certificate']['span_certificate']['disc_count']+=1
    assert not verify_transport_annulus_certificate(Diagram.from_pd(case['source']['pd']),wrong)
assert bench['completed_calls']==bench['measured_calls']==48 and bench['warmup_calls']==16
for row in bench['cases']:
    samples=row['samples']+row['warmups']
    assert all(m['completed']for sample in samples for m in sample['measurements'].values())
    for arm in ('old','old_AA','new','new_AA'):
        assert len({sample['measurements'][arm]['status']for sample in samples})==1
    if row['name']=='native/optimized-positive':
        assert all(sample['measurements']['old']['status']=='INCONCLUSIVE'and sample['measurements']['new']['status']=='UNKNOT'for sample in samples)
    if row['name'].startswith('recognition/'):
        assert all(m['status']=='UNKNOT'for sample in samples for m in sample['measurements'].values())
pilots=read('endpoint-negative-pilots.json')
assert len(pilots['records'])==4
for r in pilots['records']:
    assert r['driver_sha256']==sha256((DATA/(r['name']+'_pilot.py')).read_bytes()).hexdigest()
result=dict(runtime_revision=audit['native_runtime_revision'],source_pins=len(pins),maintained_tests=1529,focused_tests=36,
    actual_diagrams=6,disabled_exact_diagrams=6,complete_capped_fallbacks=6,
    producer_disabled_source_proofs=len(audit['diagram_proofs']),fresh_regina_surfaces=len(audit['fresh_regina_checks']),
    annulus_caps=sum(p['schema']=='diagram-transport-annulus-v1'for p in audit['diagram_proofs']),
    new_nonempty_annulus_witness=True,measured_calls=48,warmups=16,negative_pilot_policies=4)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
    start=int(re.search(r'\\newlabel\{sec:transport-annulus\}\{\{152\}\{(\d+)\}',(ROOT/'synthesis/report.aux').read_text()).group(1))
    end=int(re.search(r'\\numberline \{153\}Assessment and recommendations\}\{(\d+)\}',(ROOT/'synthesis/report.toc').read_text()).group(1))
    visual=read('transport-annulus-visual-review.json')
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,end+3))
    result.update(pdf_pages=pages,new_section_start=start,assessment_page=end,
        preexisting_overfull_warnings=warnings,visual_review=visual)
    (DATA/'transport-annulus-latex.txt').write_text('\n'.join(line.rstrip()for line in log.splitlines()).rstrip()+'\n')
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/transport_annulus.tex','synthesis/transport_annulus_results.tex',
        'synthesis/data/transport_annulus_review.py','synthesis/data/transport_annulus_tables.py',
        'fast/README.md','synthesis/README.md','synthesis/make_tables.py',
        'synthesis/tables/transport_annulus_native.tex','synthesis/tables/transport_annulus_recognition.tex']
    result['publication_sha256']={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths}
(DATA/('transport-annulus-review.json'if '--publication'in sys.argv else 'transport-annulus-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('publication_sha256','visual_review')}))
