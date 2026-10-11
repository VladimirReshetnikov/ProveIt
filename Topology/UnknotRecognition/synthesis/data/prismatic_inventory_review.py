"""Independent publication review of source-owned normal bundle inventories."""
from contextlib import ExitStack
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[2];DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_prismatic_inventory_verify import verify_normal_prismatic_inventory

def read(name):return json.loads((DATA/name).read_text())
a=read('prismatic-inventory-audit.json');b=read('prismatic-inventory-benchmark.json')
assert a['supplied_cases']==len(a['records'])==5241 and a['source_cases']==48
assert a['normal_midsection_instances']==7838 and a['regina_base_checks']==48
assert a['search_free_reused_traces']==6 and len(a['source_proofs'])==57 and len(a['large_cases'])==9
assert a['native_source_sha256']==b['native_source_sha256']
for p,h in a['native_source_sha256'].items():assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
assert a['pilot_sha256']==b['pilot_sha256']==sha256((DATA/'cut-product-pilot.json').read_bytes()).hexdigest()
assert re.search(r'Ran 1564 tests in [0-9.]+s\n\nOK',(DATA/'prismatic-inventory-tests.txt').read_text())
assert re.search(r'Ran 24 tests in [0-9.]+s\n\nOK',(DATA/'prismatic-inventory-focused.txt').read_text())
disabled=('fastunknot.normal_prismatic_inventory._prism_weights','fastunknot.normal_prismatic_inventory._inventory',
    'fastunknot.normal_cut_complement._chamber_system','fastunknot.weighted_orbits.weighted_orbit_histogram',
    'fastunknot.weighted_orbits.weighted_histogram_from_orbit_certificate','fastunknot.interval_orbits.count_orbits')
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used')))
    for row in a['source_proofs']:
        assert verify_normal_prismatic_inventory(row['triangulation'],row['coordinates'],row['certificate'])
assert b['measured_calls']==b['completed_calls']==80 and b['warmup_calls']==16
for case in b['cases']:
    n=int(case['name'].rsplit('-',1)[1])
    for sample in case['samples']+case['warmups']:
        for value in sample['measurements'].values():
            assert value['completed']
            inv=value['inventory'];assert inv['core_components']==1 and inv['prismatic_components']==n-1
            assert inv['bases']==[dict(coordinates=[[1,1,0,0,0,0,1]],multiplicity=n-1,euler_characteristic=1)]
result=dict(source_pins=len(a['native_source_sha256']),maintained_tests=1564,focused_tests=24,
    supplied_inventories=5241,midsection_instances=7838,fresh_regina_base_checks=48,
    producer_disabled_saved_proofs=57,large_binary_cases=9,search_free_reused_traces=6,
    measured_calls=80,warmups=16,full_coordinate_doubles_preserved=True,core_geometry=False,
    interior_attached_parallelity=False,recognizer_integration=False)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    start=int(re.search(r'\\newlabel\{sec:prismatic-inventory\}\{\{157\}\{(\d+)\}',(ROOT/'synthesis/report.aux').read_text()).group(1))
    end=int(re.search(r'\\numberline \{158\}Assessment and recommendations\}\{(\d+)\}',(ROOT/'synthesis/report.toc').read_text()).group(1))
    visual=read('prismatic-inventory-visual-review.json')
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,end+3))
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/prismatic_inventory.tex','synthesis/prismatic_inventory_results.tex',
        'synthesis/data/prismatic_inventory_review.py','synthesis/data/prismatic_inventory_tables.py',
        'synthesis/tables/prismatic_inventory_queries.tex','synthesis/make_tables.py','fast/README.md','synthesis/README.md']
    result.update(pdf_pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1)),
        section_start=start,assessment_page=end,visual_review=visual,preexisting_overfull_warnings=warnings,
        publication_sha256={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths})
    (DATA/'prismatic-inventory-latex.txt').write_text(log)
(DATA/('prismatic-inventory-publication-review.json'if '--publication'in sys.argv else 'prismatic-inventory-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('publication_sha256','visual_review')}))
