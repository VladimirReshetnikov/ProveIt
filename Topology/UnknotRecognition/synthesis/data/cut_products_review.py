"""Review conservative prism classification, source authority and publication."""
from contextlib import ExitStack
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
a=read('cut-products-audit.json');b=read('cut-products-benchmark.json');pilot=read('cut-product-pilot.json')
assert a['pilot_cases']==a['disabled_exact_cases']==pilot['surface_cases']==5241
assert a['normal_midsections_checked']==pilot['normal_midsections_checked']==7838
assert a['legacy_proofs']==157 and a['source_cases']==48
assert len(a['source_proofs'])==55 and len(a['large_cases'])==7
assert a['native_source_sha256']==b['native_source_sha256']
for p,h in a['native_source_sha256'].items():assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
assert a['pilot_sha256']==b['pilot_sha256']==sha256((DATA/'cut-product-pilot.json').read_bytes()).hexdigest()
assert pilot['driver_sha256']==sha256((DATA/'cut_product_pilot.py').read_bytes()).hexdigest()
assert pilot['input_pilot_sha256']==sha256((DATA/'complement-chamber-pilot.json').read_bytes()).hexdigest()
assert pilot['corpus_sha256']==sha256((ROOT/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest()
assert re.search(r'Ran 1555 tests in [0-9.]+s\n\nOK',(DATA/'cut-products-tests.txt').read_text())
assert re.search(r'Ran 15 tests in [0-9.]+s\n\nOK',(DATA/'cut-products-focused.txt').read_text())
for r in a['records']:
    assert r['cut_components']==r['core_components']+r['product_components']
    assert 1<=r['core_components']<=r['marked_chambers']
for r in a['large_cases']:
    assert r['core_components']==1 and encoded_integer(r['prismatic_components'])==(1<<r['bits'])-1
disabled=('fastunknot.normal_cut_complement._exceptional_chambers',
    'fastunknot.normal_cut_complement._chamber_system','fastunknot.interval_orbits.count_orbits')
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used during replay')))
    for r in a['source_proofs']:
        assert verify_normal_complement_certificate(r['triangulation'],r['coordinates'],r['certificate'])
assert b['measured_calls']==b['completed_calls']==80 and b['warmup_calls']==16
for case in b['cases']:
    n=int(case['name'].rsplit('-',1)[1])
    for sample in case['samples']+case['warmups']:
        for m in sample['measurements'].values():
            assert m['completed']and m['cut_components']==n and m['core_components']==1 and m['prismatic_components']==n-1
result=dict(source_pins=len(a['native_source_sha256']),maintained_tests=1555,focused_tests=15,
    classified_cases=5241,disabled_exact_cases=5241,normal_midsections_checked=7838,
    legacy_proofs=157,producer_disabled_saved_proofs=55,large_binary_cases=7,measured_calls=80,warmups=16,
    conservative_core_bound='6T',unpatterned_component_type_bound='6T+v+2q<=12T',
    maximal_parallelity_bundle=False,core_geometry_extracted=False,recognizer_integration=False)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    start=int(re.search(r'\\newlabel\{sec:cut-products\}\{\{156\}\{(\d+)\}',(ROOT/'synthesis/report.aux').read_text()).group(1))
    end=int(re.search(r'\\numberline \{157\}Assessment and recommendations\}\{(\d+)\}',(ROOT/'synthesis/report.toc').read_text()).group(1))
    visual=read('cut-products-visual-review.json')
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,end+3))
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/cut_products.tex','synthesis/cut_products_results.tex',
        'synthesis/data/cut_products_review.py','synthesis/data/cut_products_tables.py','synthesis/data/cut-products-literature.json',
        'synthesis/tables/cut_products_classification.tex','synthesis/make_tables.py','fast/README.md','synthesis/README.md']
    result.update(pdf_pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1)),
        section_start=start,assessment_page=end,visual_review=visual,preexisting_overfull_warnings=warnings,
        publication_sha256={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths})
    (DATA/'cut-products-latex.txt').write_text(log)
(DATA/('cut-products-publication-review.json'if '--publication'in sys.argv else 'cut-products-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('publication_sha256','visual_review')}))
