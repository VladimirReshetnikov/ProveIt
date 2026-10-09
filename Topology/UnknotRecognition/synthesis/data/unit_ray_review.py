"""Recheck the preserved mathematics, source pins, replay and publication."""
from contextlib import ExitStack
from hashlib import sha256
import json
from pathlib import Path
import re
import runpy
import subprocess
import sys
from types import ModuleType
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_disk_kernel import verify_normal_disk_count_certificate

audit=json.loads((DATA/'unit-ray-audit.json').read_text())
bench=json.loads((DATA/'unit-ray-benchmark.json').read_text())
for record in (audit,bench):
    assert len(record['source_sha256'])==553
    for p,h in record['source_sha256'].items():
        assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
assert audit['source_sha256']==bench['source_sha256']
assert len(audit['cases'])==audit['legacy_exact_comparisons']==2550
assert sum(r['unit_ray'] for r in audit['cases'])==audit['unit_cases']==1878
assert all(not r['unit_ray'] or r['new_cycles']==0 for r in audit['cases'])
assert all(r['unit_ray'] or (r['old_cycles'],r['old_bytes'])==
           (r['new_cycles'],r['new_bytes']) for r in audit['cases'])
assert len(audit['examples'])==44
frozen_path='Topology/UnknotRecognition/fast/fastunknot/normal_disk_kernel.py'
frozen_source=subprocess.check_output(['git','show',audit['baseline']+':'+frozen_path],cwd=ROOT)
assert sha256(frozen_source).hexdigest()==audit['baseline_source_sha256']==bench['baseline_source_sha256']
old=ModuleType('_unit_ray_review_old');old.__package__='fastunknot'
exec(compile(frozen_source,audit['baseline']+':'+frozen_path,'exec'),old.__dict__)
disabled=['fastunknot.normal_disk_kernel.normal_compressing_disk_count',
    'fastunknot.normal_disk_kernel.canonical_disk_core',
    'fastunknot.normal_surface_components.normal_component_census',
    'fastunknot.normal_support_peeling.peel_support_ray',
    'fastunknot.interval_orbits.count_orbits','fastunknot.interval_orbits._count_orbits']
with ExitStack() as stack:
    for name in disabled:
        stack.enter_context(patch(name,side_effect=AssertionError('producer called in replay')))
    legacy=0
    for row in audit['examples']:
        assert verify_normal_disk_count_certificate(row['triangulation'],row['coordinates'],row['certificate'])
        if row['certificate']['schema']=='normal-disc-count-v1':
            assert old.verify_normal_disk_count_certificate(row['triangulation'],row['coordinates'],row['certificate'])
            legacy+=1
assert legacy>0
for name in ('normal_support_peeling.py','normal_support_peeling_verify.py'):
    assert (ROOT/'fast/fastunknot'/name).read_bytes()==(ROOT/'reports/69/repo_overlay/Topology/UnknotRecognition/fast/fastunknot'/name).read_bytes()
assert bench['measured_calls']==bench['completed_calls']==220 and bench['warmup_calls']==44
runpy.run_path(str(DATA/'unit_ray_tables.py'))
assert 'Ran 1317 tests in 236.139s\n\nOK' in (DATA/'unit-ray-tests.txt').read_text()
assert 'Ran 34 tests in 2.896s\n\nOK' in (DATA/'unit-ray-focused-tests.txt').read_text()

placement=json.loads((DATA/'incoming-fe88-placement.json').read_text())
assert [r['report'] for r in placement]==list(range(64,70))
assert [r['placed_files'] for r in placement]==[33,33,45,649,652,702]
placed=0
for row in placement:
    assert row['crc_verified']
    report=ROOT/'reports'/str(row['report'])
    for p,h in row['file_sha256'].items():
        assert sha256((report/p).read_bytes()).hexdigest()==h,(row['report'],p)
        placed+=1
    assert row['placed_files']==len(row['file_sha256'])
    assert not (ROOT.parents[1]/'docs/incoming'/row['archive']).exists()
provenance=json.loads((ROOT/'reports/67/PROVENANCE.json').read_text())
for row in provenance['new_patch_files']:
    assert sha256((ROOT/'reports/67'/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
expected={64:(18,0.271),65:(36,1.847),66:(55,7.657)}
for number,(count,seconds) in expected.items():
    log=(DATA/f'incoming-fe88-{number}-tests.txt').read_text()
    assert f'Ran {count} tests in {seconds:.3f}s\n\nOK' in log,(number,log[-300:])
math64=json.loads((DATA/'incoming-fe88-64-audit.json').read_text())
assert [math64[k] for k in ('partition_pair_checks','incidence_minor_checks','weighted_completion_queries',
    'independent_certificates','ribbon_surface_checks','mobius_projection_checks','staged_join_queries')]==[
    44168,1155,3336,72,2000,5295,1800]
math65=json.loads((DATA/'incoming-fe88-65-audit.json').read_text())
assert [math65[k] for k in ('direct_matrix_pairs','weighted_families','weighted_completion_queries',
    'literal_surface_cases','complete_grammar_comparisons')]==[813297,1000,14014,1000,200]
math66=json.loads((DATA/'incoming-fe88-66-audit.json').read_text())
assert [math66[k] for k in ('test_methods','errors','failures','exhaustive_signed_matrix_entries',
    'triangulated_seam_gluings','exhaustive_patch_assignments')]==[55,0,0,68581,442,297]
assert math66['source_unchanged_during_audit']
runpy.run_path(str(DATA/'incoming_fe88_transport_math.py'))
transport=json.loads((DATA/'incoming-fe88-transport-math.json').read_text())
assert transport['before']==dict(components=1,euler=1,pieces=24)
assert transport['after']==dict(components=3,euler=5,pieces=19)

log=(ROOT/'synthesis/report.log').read_text()
assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
assert warnings==[f'{x}pt too wide' for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
aux=(ROOT/'synthesis/report.aux').read_text()
sections={name:int(re.search(r'\\newlabel\{'+label+r'\}\{\{'+str(number)+r'\}\{(\d+)\}',aux).group(1))
    for name,label,number in [('mathematics','sec:completion-theorems',128),('unit_ray','sec:unit-ray-native',129)]}
toc=(ROOT/'synthesis/report.toc').read_text()
end=int(re.search(r'\\numberline \{130\}Assessment and recommendations\}\{(\d+)\}',toc).group(1))
assert pages>=513 and 500<=sections['mathematics']<sections['unit_ray']<end
visual=json.loads((DATA/'unit-ray-visual-review.json').read_text())
assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
assert visual['rendered_pages']==visual['inspected_pages']==list(range(sections['mathematics'],end+1))
(DATA/'unit-ray-latex.txt').write_text('\n'.join(line.rstrip() for line in log.splitlines()).rstrip()+'\n')
paths=['synthesis/report.pdf','synthesis/report.tex','synthesis/make_tables.py','fast/README.md','reports/README.md',
    'synthesis/README.md','synthesis/completion_theorems.tex','synthesis/unit_ray.tex',
    'synthesis/tables/unit_ray_count.tex','synthesis/tables/unit_ray_sector.tex',
    'synthesis/data/unit_ray_review.py','synthesis/data/unit_ray_tables.py','synthesis/data/incoming_fe88_transport_math.py']
paths += [str(p.relative_to(ROOT)) for p in DATA.glob('unit-ray-*') if p.name!='unit-ray-review.json']
paths += [str(p.relative_to(ROOT)) for p in DATA.glob('incoming-fe88-*')]
result=dict(runtime_revision='eae26c218',preserved_reports=list(range(64,70)),preserved_files=placed,
    preserved_patch_hashes_67=len(provenance['new_patch_files']),standalone_tests_64_66=109,
    mathematical_transport_height_cases=3125,source_pins_per_dataset=553,maintained_tests=1317,
    focused_tests=34,corpus_configurations=2550,unit_configurations=1878,
    producer_disabled_retained_proofs=44,retained_legacy_proofs=legacy,
    benchmark_measured=220,benchmark_warmups=44,pdf_pages=pages,section_starts=sections,
    new_section_pages=list(range(sections['mathematics'],end+1)),preexisting_overfull_warnings=warnings,
    sha256={p:sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)})
(DATA/'unit-ray-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='sha256'}))
