"""Review source-labelled prism interfaces and incomplete-topology scope."""
from contextlib import ExitStack
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[2];DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_prism_interfaces_verify import verify_normal_prism_interfaces

def read(name):return json.loads((DATA/name).read_text())
a=read('prism-interfaces-audit.json');b=read('prism-interfaces-benchmark.json')
assert a['supplied_cases']==a['previous_unattached_counts_preserved']==len(a['records'])==5289
assert a['mixed_cases']==48 and len(a['inside_core_cases'])==4 and len(a['large_cases'])==7
assert len(a['source_proofs'])==a['attached_source_cases']+11
assert a['native_source_sha256']==b['native_source_sha256']
for p,h in a['native_source_sha256'].items():assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
assert a['pilot_sha256']==b['pilot_sha256']==sha256((DATA/'cut-product-pilot.json').read_bytes()).hexdigest()
assert re.search(r'Ran 1571 tests in [0-9.]+s\n\nOK',(DATA/'prism-interfaces-tests.txt').read_text())
assert re.search(r'Ran 31 tests in [0-9.]+s\n\nOK',(DATA/'prism-interfaces-focused.txt').read_text())
inside=next(r for r in a['inside_core_cases']if r['tetrahedra']==16)
assert inside['regions']==3 and inside['ports']==30 and inside['unattached_components']==0
with ExitStack()as stack:
    for name in ('fastunknot.normal_prism_interfaces._interface_system','fastunknot.normal_prism_interfaces._profiles',
                 'fastunknot.weighted_orbits.weighted_orbit_histogram','fastunknot.interval_orbits.count_orbits'):
        stack.enter_context(patch(name,side_effect=AssertionError('producer used')))
    for r in a['source_proofs']:
        assert verify_normal_prism_interfaces(r['triangulation'],r['coordinates'],r['certificate'])
        s=r['certificate']['structure'];t=len(r['triangulation']['tetrahedra'])
        assert len(s['core_cells'])<=6*t and len(s['ports'])<=24*t
        assert sorted(i for row in s['attached_regions']for i in row['ports'])==list(range(len(s['ports'])))
assert b['measured_calls']==b['completed_calls']==80 and b['warmup_calls']==16
for case in b['cases']:
    samples=case['samples']+case['warmups']
    assert len({v['structure_sha256']for sample in samples for v in sample['measurements'].values()})==1
    assert all(v['completed']for sample in samples for v in sample['measurements'].values())
result=dict(source_pins=len(a['native_source_sha256']),maintained_tests=1571,focused_tests=31,
    supplied_structures=5289,mixed_cases=48,attached_source_cases=a['attached_source_cases'],
    producer_disabled_saved_proofs=len(a['source_proofs']),inside_core_cases=4,large_binary_cases=7,
    measured_calls=80,warmups=16,ribbon_01_profiles_only=True,edge_vertex_handles=False,
    maximal_parallelity_bundle=False,ordered_boundary_curves=False,recognizer_integration=False)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    start=int(re.search(r'\\newlabel\{sec:prism-interfaces\}\{\{158\}\{(\d+)\}',(ROOT/'synthesis/report.aux').read_text()).group(1))
    end=int(re.search(r'\\numberline \{159\}Assessment and recommendations\}\{(\d+)\}',(ROOT/'synthesis/report.toc').read_text()).group(1))
    visual=read('prism-interfaces-visual-review.json')
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,end+3))
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/prism_interfaces.tex','synthesis/prism_interfaces_results.tex',
        'synthesis/data/prism_interfaces_review.py','synthesis/data/prism_interfaces_tables.py',
        'synthesis/tables/prism_interfaces_queries.tex','synthesis/make_tables.py','fast/README.md','synthesis/README.md']
    result.update(pdf_pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1)),
        section_start=start,assessment_page=end,visual_review=visual,preexisting_overfull_warnings=warnings,
        publication_sha256={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths})
    (DATA/'prism-interfaces-latex.txt').write_text(log)
(DATA/('prism-interfaces-publication-review.json'if '--publication'in sys.argv else 'prism-interfaces-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('publication_sha256','visual_review')}))
