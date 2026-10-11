"""Review exact on-demand footprint membership and original source proofs."""
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
from fastunknot.pachner_cover_verify import verify_pachner_cover,inspect_pachner_descent
from fastunknot.normal_transport_verify import verify_transport_disk_certificate

def read(name):return json.loads((DATA/name).read_text())
def frozen(revision,pins,current=False):
    prefix='Topology/UnknotRecognition/'
    raw=subprocess.check_output(['git','archive',revision]+[prefix+p for p in pins],cwd=ROOT.parents[1])
    with tarfile.open(fileobj=BytesIO(raw))as archive:
        for p,h in pins.items():
            assert sha256(archive.extractfile(prefix+p).read()).hexdigest()==h,p
            if current:assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p

audit=read('cover-oracle-audit.json');source_bench=read('cover-oracle-source-benchmark.json')
diagram_bench=read('cover-oracle-diagram-benchmark.json');pins=audit['native_source_sha256']
assert pins==source_bench['native_source_sha256']==diagram_bench['native_source_sha256']
frozen(audit['native_runtime_revision'],pins,True)
assert len(audit['source_cases'])==2
assert audit['disabled_exact_cases']==len(audit['diagram_cases'])==13
assert all(r['disabled_status']==r['enabled_status']==r['source']['expected']for r in audit['diagram_cases'])
assert audit['fresh_regina_disc_checks']==len(audit['diagram_proofs'])
assert re.search(r'Ran 1506 tests in [0-9.]+s\n\nOK',(DATA/'cover-oracle-tests.txt').read_text())
assert re.search(r'Ran 27 tests in [0-9.]+s\n\nOK',(DATA/'cover-oracle-focused.txt').read_text())
for case in audit['source_cases']:
    assert case['negative']['status']=='COMPLETE_BOUNDED_DESCENT'
    assert case['descent']['status']=='DESCENT_FOUND'
    assert case['new_stats']['regions_indexed']==0 and case['new_stats']['cover_backend']=='oracle'
    assert case['new_stats']['nodes']==case['old_stats']['nodes']
    assert case['regina']=={'before':True,'after':True}
disabled=('fastunknot.pachner_cover_search.search_pachner_cover','fastunknot.pachner_cover_search.find_pachner_descent',
    'fastunknot.pachner_cover_oracle._CoverOracle.complete','fastunknot.pachner_cover_oracle._CoverOracle.extend',
    'fastunknot.pachner_regions.search_pachner_regions','fastunknot.pachner_commitments.search_pachner_endpoints',
    'fastunknot.pachner_commitments._advance','fastunknot.pachner23.pachner_23','fastunknot.pachner32.pachner_32',
    'fastunknot.cocycle_transport.transport_cocycle','fastunknot.cocycle_transport.descend_cocycle',
    'fastunknot.normal_cocycle.rank_one_cocycle_seed','fastunknot.diagram_exterior.diagram_exterior',
    'fastunknot.normal_disk_kernel.normal_compressing_disk_count','fastunknot.normal_pachner_search.pachner_seed_decide')
replays=0
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used during independent replay')))
    for case in audit['source_cases']:
        raw=case['source']['triangulation'];h=case['source']['heights']
        for proof in case['endpoints']:
            assert verify_pachner_cover(raw,h,proof,max_region_size=6,max_upward=1);replays+=1
        assert inspect_pachner_descent(raw,h,case['descent']['certificate'],max_upward=1)
    for proof in audit['diagram_proofs']:
        assert verify_transport_disk_certificate(Diagram.from_pd(proof['input_pd']),proof)
assert replays==audit['independent_endpoint_replays']
for data,calls,warm in ((source_bench,40,8),(diagram_bench,160,32)):
    assert data['completed_calls']==data['measured_calls']==calls and data['warmup_calls']==warm
    for case in data['cases']:
        for sample in case['samples']+case['warmups']:
            assert all(m['completed']for m in sample['measurements'].values())
            if case['name'].startswith('recognition/')or case['name'].startswith('descent-'):
                assert len({m['status']for m in sample['measurements'].values()})==1
probe=read('cover-oracle-index-probe.json')
assert probe['driver_sha256']==sha256((DATA/'cover_oracle_index_probe.py').read_bytes()).hexdigest()
assert len(probe['records'])==3 and all(r['index_completed']is False for r in probe['records'])
result=dict(runtime_revision=audit['native_runtime_revision'],source_pins=len(pins),maintained_tests=1506,
    focused_tests=27,source_fixtures=2,independent_endpoint_replays=replays,strict_descents=2,
    disabled_exact_diagrams=13,enabled_complete_verdicts=13,
    producer_disabled_diagram_proofs=len(audit['diagram_proofs']),fresh_regina_discs=audit['fresh_regina_disc_checks'],
    old_completed_diagram_moves=sum(r['old_progress']['completed_moves']for r in audit['diagram_cases']),
    new_completed_diagram_moves=sum(r['new_progress']['completed_moves']for r in audit['diagram_cases']),
    source_measured_calls=40,source_warmups=8,diagram_measured_calls=160,diagram_warmups=32)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
    start=int(re.search(r'\\newlabel\{sec:cover-oracle\}\{\{149\}\{(\d+)\}',(ROOT/'synthesis/report.aux').read_text()).group(1))
    end=int(re.search(r'\\numberline \{150\}Assessment and recommendations\}\{(\d+)\}',(ROOT/'synthesis/report.toc').read_text()).group(1))
    visual=read('cover-oracle-visual-review.json')
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,end+3))
    result.update(pdf_pages=pages,new_section_start=start,assessment_page=end,
        preexisting_overfull_warnings=warnings,visual_review=visual)
    (DATA/'cover-oracle-latex.txt').write_text('\n'.join(line.rstrip()for line in log.splitlines()).rstrip()+'\n')
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/cover_oracle.tex','synthesis/cover_oracle_results.tex',
        'synthesis/data/cover_oracle_review.py','synthesis/data/cover_oracle_tables.py','synthesis/data/cover_oracle_index_probe.py',
        'fast/README.md','synthesis/README.md','synthesis/pachner_native.tex','synthesis/make_tables.py',
        'synthesis/tables/cover_oracle_sources.tex','synthesis/tables/cover_oracle_queries.tex','synthesis/tables/cover_oracle_recognition.tex']
    result['publication_sha256']={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths}
(DATA/('cover-oracle-review.json'if '--publication'in sys.argv else 'cover-oracle-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('publication_sha256','visual_review')}))
