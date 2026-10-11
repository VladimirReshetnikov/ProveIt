"""Review explicit per-epoch reach and full original-diagram proof chains."""
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
from fastunknot.normal_transport_verify import verify_transport_disk_certificate

def read(name):return json.loads((DATA/name).read_text())
def frozen(revision,pins,current=False):
    prefix='Topology/UnknotRecognition/'
    raw=subprocess.check_output(['git','archive',revision]+[prefix+p for p in pins],cwd=ROOT.parents[1])
    with tarfile.open(fileobj=BytesIO(raw))as archive:
        for p,h in pins.items():
            assert sha256(archive.extractfile(prefix+p).read()).hexdigest()==h,p
            if current:assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p

audit=read('pachner-epochs-audit.json');bench=read('pachner-epochs-benchmark.json')
pins=audit['native_source_sha256'];assert pins==bench['native_source_sha256']
frozen(audit['native_runtime_revision'],pins,True)
assert audit['disabled_exact_cases']==len(audit['diagram_cases'])==6
assert audit['fresh_regina_disc_checks']==len(audit['diagram_proofs'])
assert re.search(r'Ran 1514 tests in [0-9.]+s\n\nOK',(DATA/'pachner-epochs-tests.txt').read_text())
assert re.search(r'Ran 26 tests in [0-9.]+s\n\nOK',(DATA/'pachner-epochs-focused.txt').read_text())
case=next(r for r in audit['diagram_cases']if r['source']['name']=='genus-one-miss')
assert case['old_status']=='INCONCLUSIVE'and case['new_status']=='UNKNOT'
assert case['enabled_positive_method']=='native-pachner-epochs'
stats=case['new_stats'];assert stats['epochs']==33 and stats['initial_tetrahedra']==54 and stats['remaining_tetrahedra']==21
assert (stats['upward_moves'],stats['downward_moves'])==(9,42)and len(case['certificate']['steps'])==51
for r in audit['diagram_cases']:
    assert r['disabled_status']==r['enabled_capped_status']==r['source']['expected']
    assert all(e['after']<e['before']and e['upward_moves']<=1 for e in r['new_stats']['epoch_records'])
    assert r['new_stats']['nodes']<=1000
disabled=('fastunknot.pachner_epochs.pachner_epoch_seed_decide','fastunknot.pachner_epochs.find_pachner_descent',
    'fastunknot.pachner_cover_search.find_pachner_descent','fastunknot.pachner_cover_search.search_pachner_cover',
    'fastunknot.pachner23.pachner_23','fastunknot.pachner32.pachner_32',
    'fastunknot.cocycle_transport.transport_cocycle','fastunknot.cocycle_transport.descend_cocycle',
    'fastunknot.diagram_exterior.diagram_exterior','fastunknot.normal_disk_kernel.normal_compressing_disk_count')
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used during full-chain replay')))
    for proof in audit['diagram_proofs']:
        assert verify_transport_disk_certificate(Diagram.from_pd(proof['input_pd']),proof)
    wrong=deepcopy(case['certificate']);wrong['steps'].pop(1)
    assert not verify_transport_disk_certificate(Diagram.from_pd(case['source']['pd']),wrong)
assert bench['completed_calls']==bench['measured_calls']==48 and bench['warmup_calls']==16
for row in bench['cases']:
    samples=row['samples']+row['warmups']
    assert all(m['completed']for sample in samples for m in sample['measurements'].values())
    for arm in ('old','old_AA','new','new_AA'):
        assert len({sample['measurements'][arm]['status']for sample in samples})==1
    if row['name']=='native/genus-one-miss':
        assert all(sample['measurements']['old']['status']=='INCONCLUSIVE'and sample['measurements']['new']['status']=='UNKNOT'for sample in samples)
    if row['name'].startswith('recognition/'):
        assert all(m['status']=='UNKNOT'for sample in samples for m in sample['measurements'].values())
order=read('epoch-order-pilot.json')
assert order['trials']==8 and order['new_positive_witnesses']==0
assert order['driver_sha256']==sha256((DATA/'epoch_order_pilot.py').read_bytes()).hexdigest()
result=dict(runtime_revision=audit['native_runtime_revision'],source_pins=len(pins),maintained_tests=1514,focused_tests=26,
    actual_diagrams=6,disabled_exact_diagrams=6,complete_capped_fallbacks=6,
    producer_disabled_diagram_proofs=len(audit['diagram_proofs']),fresh_regina_discs=audit['fresh_regina_disc_checks'],
    new_nonempty_epoch_witness=True,verified_epochs=33,initial_tetrahedra=54,final_tetrahedra=21,
    upward_moves=9,downward_moves=42,full_chain_steps=51,measured_calls=48,warmups=16,failed_ordering_trials=8)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
    start=int(re.search(r'\\newlabel\{sec:pachner-epochs\}\{\{150\}\{(\d+)\}',(ROOT/'synthesis/report.aux').read_text()).group(1))
    end=int(re.search(r'\\numberline \{151\}Assessment and recommendations\}\{(\d+)\}',(ROOT/'synthesis/report.toc').read_text()).group(1))
    visual=read('pachner-epochs-visual-review.json')
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,end+3))
    result.update(pdf_pages=pages,new_section_start=start,assessment_page=end,
        preexisting_overfull_warnings=warnings,visual_review=visual)
    (DATA/'pachner-epochs-latex.txt').write_text('\n'.join(line.rstrip()for line in log.splitlines()).rstrip()+'\n')
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/pachner_epochs.tex','synthesis/pachner_epochs_results.tex',
        'synthesis/data/pachner_epochs_review.py','synthesis/data/pachner_epochs_tables.py',
        'fast/README.md','synthesis/README.md','synthesis/make_tables.py',
        'synthesis/tables/pachner_epochs_native.tex','synthesis/tables/pachner_epochs_recognition.tex']
    result['publication_sha256']={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths}
(DATA/('pachner-epochs-review.json'if '--publication'in sys.argv else 'pachner-epochs-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('publication_sha256','visual_review')}))
