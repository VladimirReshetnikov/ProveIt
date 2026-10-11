"""Independent current-source review of compressed cut connectivity evidence."""
from contextlib import ExitStack
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[2];DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.integer_codec import encoded_integer
from fastunknot.normal_cut_complement_verify import verify_normal_complement_certificate

def read(name):return json.loads((DATA/name).read_text())
audit=read('cut-complement-audit.json');bench=read('cut-complement-benchmark.json');pilot=read('complement-chamber-pilot.json')
assert audit['source_cases']==pilot['source_cases']==48
assert audit['pilot_surfaces']==pilot['surface_cases']==1635
assert audit['mixed_surfaces']==384 and audit['regina_cut_checks']==2019
assert audit['large_binary_cases']==len(audit['large_cases'])==13
assert len(audit['source_proofs'])==157
assert audit['native_source_sha256']==bench['native_source_sha256']
for p,h in audit['native_source_sha256'].items():assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
assert audit['pilot_sha256']==bench['pilot_sha256']==sha256((DATA/'complement-chamber-pilot.json').read_bytes()).hexdigest()
assert audit['corpus_sha256']==bench['corpus_sha256']==pilot['corpus_sha256']
assert pilot['corpus_sha256']==sha256((ROOT/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest()
assert pilot['driver_sha256']==sha256((DATA/'complement_chamber_pilot.py').read_bytes()).hexdigest()
expected={(r['id'],r['index']):r for r in pilot['records']}
for row in audit['records']:
    old=expected[row['id'],row['index']]
    assert row['components']==old['components']and row['chamber_points']==old['chamber_points']
    assert row['normal_discs']==old['normal_discs']and row['cut_tetrahedra']==old['expanded_cut_tetrahedra']
for row in audit['large_cases']:
    bits=row['scale_bits'];count=encoded_integer(row['components'])
    if row['kind']in ('parallel-meridian','meridian'):assert count==1<<bits
    elif row['kind']=='vertex-link':assert count==(1<<bits)+1
    else:assert count==(1<<(bits-1))+1
    assert row['pairings']<=20*row['tetrahedra']
disabled=('fastunknot.normal_cut_complement._chamber_system',
    'fastunknot.normal_cut_complement.normal_complement_components','fastunknot.interval_orbits.count_orbits')
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used in replay')))
    for record in audit['source_proofs']:
        assert verify_normal_complement_certificate(record['triangulation'],record['coordinates'],record['certificate'])
    wrong=deepcopy(audit['source_proofs'][-1]);wrong['certificate']['cut_components']=1
    assert not verify_normal_complement_certificate(wrong['triangulation'],wrong['coordinates'],wrong['certificate'])
assert re.search(r'Ran 1548 tests in [0-9.]+s\n\nOK',(DATA/'cut-complement-tests.txt').read_text())
assert re.search(r'Ran 8 tests in [0-9.]+s\n\nOK',(DATA/'cut-complement-focused.txt').read_text())
assert bench['completed_calls']==bench['measured_calls']==80 and bench['warmup_calls']==16
for case in bench['cases']:
    expected_count=int(case['name'].rsplit('-',1)[1])
    for sample in case['samples']+case['warmups']:
        assert all(m['completed']and m['cut_components']==expected_count for m in sample['measurements'].values())
        for arm in ('new','new_AA'):
            assert sample['measurements'][arm]['interval_pairings']==3
            assert sample['measurements'][arm]['cycles']==4
result=dict(source_pins=len(audit['native_source_sha256']),maintained_tests=1548,focused_tests=8,
    source_cases=48,regina_cut_checks=2019,mixed_surfaces=384,large_binary_cases=13,
    producer_disabled_saved_proofs=157,measured_calls=80,warmups=16,
    bit_polynomial_component_count_only=True,full_cut_geometry=False,recognizer_integration=False)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    start=int(re.search(r'\\newlabel\{sec:cut-complement\}\{\{155\}\{(\d+)\}',(ROOT/'synthesis/report.aux').read_text()).group(1))
    end=int(re.search(r'\\numberline \{156\}Assessment and recommendations\}\{(\d+)\}',(ROOT/'synthesis/report.toc').read_text()).group(1))
    visual=read('cut-complement-visual-review.json')
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,end+3))
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/cut_complement.tex',
        'synthesis/cut_complement_results.tex','synthesis/data/cut_complement_review.py',
        'synthesis/data/cut_complement_tables.py','synthesis/tables/cut_complement_counts.tex',
        'synthesis/make_tables.py','synthesis/README.md','fast/README.md']
    result.update(pdf_pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1)),
        section_start=start,assessment_page=end,visual_review=visual,preexisting_overfull_warnings=warnings,
        publication_sha256={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths})
    (DATA/'cut-complement-latex.txt').write_text(log)
(DATA/('cut-complement-publication-review.json'if '--publication'in sys.argv else 'cut-complement-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('publication_sha256','visual_review')}))
