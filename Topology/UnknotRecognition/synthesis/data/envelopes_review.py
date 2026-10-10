"""Recheck native envelopes, preserved mathematical evidence and publication."""
from contextlib import ExitStack
from hashlib import sha256
import json
from pathlib import Path
import re
import runpy
import subprocess
import sys
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[2];DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.sector_envelope_verify import verify_sector_envelope_certificate
from fastunknot.normal_disk_kernel import verify_normal_disk_count_certificate

audit=json.loads((DATA/'envelopes-audit.json').read_text())
bench=json.loads((DATA/'envelopes-benchmark.json').read_text())
family=json.loads((DATA/'envelopes-family.json').read_text())
for record in (audit,bench):
    assert len(record['native_source_sha256'])==567
    assert record['native_source_sha256']==audit['native_source_sha256']
    for p,h in record['native_source_sha256'].items():assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
for p,h in family['native_source_sha256'].items():assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
assert audit['counts']['selected']==9995 and audit['counts']['audited']==9344
assert audit['automatic_comparisons']==9360 and audit['fresh_regina_full_enumerations']==15
assert audit['counts']['rays']==4853 and audit['counts']['interior_rays']==804
assert family['counts']==dict(ray_families=9,topology_vectors=97)
source=subprocess.check_output(['git','show',audit['native_baseline']+
    ':Topology/UnknotRecognition/fast/fastunknot/normal_sector.py'],cwd=ROOT)
assert sha256(source).hexdigest()==audit['native_baseline_source_sha256']==bench['native_baseline_source_sha256']
for name in ('sector_envelope.py','sector_envelope_certificate.py','sector_envelope_verify.py'):
    assert (ROOT/'fast/fastunknot'/name).read_bytes()==(ROOT/'reports/74/code/fastunknot'/name).read_bytes()
original=json.loads((ROOT/'reports/74/results/independent_envelope_audit.json').read_text())
coverage=json.loads((ROOT/'reports/74/results/coverage.json').read_text())
retained=[(r['triangulation'],r['certificate']) for r in original['records'] if r.get('certificate') is not None]
assert len(retained)==60
retained += [(r['fixture']['triangulation'],r['certificate']) for r in coverage['certificates']]
assert len(retained)==66
retained += [(r['source']['triangulation'],r['certificate']) for r in bench['coverage_capacity']]
assert len(retained)==70
disabled=['fastunknot.normal_sector.build_sector_kernel','fastunknot.normal_sector.sector_rays',
    'fastunknot.normal_sector._hyperplanes','fastunknot.normal_sector._support_rays',
    'fastunknot.sector_envelope.sector_envelope_plan','fastunknot.sector_envelope.sector_envelope_rays',
    'fastunknot.sector_envelope_certificate.certify_sector_enumeration',
    'fastunknot.normal_disk_kernel.normal_compressing_disk_count','fastunknot.normal_disk_kernel.canonical_disk_core',
    'fastunknot.normal_support_peeling.peel_support_ray','fastunknot.interval_orbits.count_orbits',
    'fastunknot.interval_orbits._count_orbits']
with ExitStack() as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer called in replay')))
    for raw,certificate in retained:assert verify_sector_envelope_certificate(raw,certificate)
    extra=audit['extra_disc_example']
    assert verify_normal_disk_count_certificate(extra['triangulation'],extra['coordinates'],extra['disk_certificate'])
assert bench['completed_calls']==bench['measured_calls']==260 and bench['warmup_calls']==52
runpy.run_path(str(DATA/'envelopes_tables.py'))
assert 'Ran 1351 tests in 224.903s\n\nOK' in (DATA/'envelopes-tests.txt').read_text()
assert 'Ran 42 tests in 3.481s\n\nOK' in (DATA/'envelopes-focused.txt').read_text()
for n,count,seconds in ((70,34,2.413),(71,42,1.058),(72,42,0.656)):
    assert f'Ran {count} tests in {seconds:.3f}s\n\nOK' in (DATA/f'incoming-818-{n}-tests.txt').read_text()
affine=json.loads((DATA/'incoming-818-70-audit.json').read_text())
assert affine['status']=='PASS' and affine['counts']['models']==2000
assert affine['counts']['certificate_replays']==2000
cycle=json.loads((DATA/'incoming-818-71-audit.json').read_text())
assert cycle['all_checks_passed'] and cycle['matrix_entries']==633531 and cycle['envelope_cases']==3162
assert cycle['weighted_queries']==16904 and cycle['literal_assignments']==1412
rooted=json.loads((DATA/'incoming-818-72-audit.json').read_text())
assert rooted['weighted_optimum_queries']==10000 and rooted['languages']['literal_assignments']==3200
assert rooted['languages']['complete_language_certificates']==200
assert 'Ran 56 tests in 3.823s\n\nOK (skipped=5)' in (DATA/'incoming-818-73-tests.txt').read_text()
assert 'Ran 5 tests in 1.000s\n\nOK' in (DATA/'incoming-818-73-optional-tests.txt').read_text()
active=json.loads((DATA/'incoming-818-73-active-replay.json').read_text())
assert active['support_certificates_verified']==37 and active['normal_search_certificates_verified']==7
assert active['solver_used'] is False
geometry=json.loads((DATA/'incoming-818-73-geometric-replay.json').read_text())
assert geometry['passed'] and geometry['producer_call_guard']
assert geometry['benchmark_batch_transports']==24 and geometry['benchmark_sequential_transports']==500
assert geometry['counterexample']['peeled_gains']==dict(first=1,second=1,combined=0)
reproduction=json.loads((DATA/'incoming-818-74-run_report.json').read_text())
assert reproduction['status']=='COMPLETE' and reproduction['focused_tests']==24
assert reproduction['certificate_replay']['independent_envelope_certificates']==60
assert reproduction['certificate_replay']['enumeration_producers_blocked']
assert 'Ran 29 tests in 29.570s\n\nOK (skipped=1)' in (DATA/'incoming-818-75-tests.txt').read_text()
assert re.search(r'Ran 1 test in .*s\n\nOK', (DATA/'incoming-818-75-optional-test.txt').read_text())
for name,count in [('geometric-replay',91),('benchmark-replay',126)]:
    assert json.loads((DATA/f'incoming-818-75-{name}.json').read_text())['accepted']==count
regina=json.loads((DATA/'incoming-818-75-regina.json').read_text())
assert regina['source_states']==23 and regina['checked_replacements']==176 and regina['mismatch_count']==0
region=json.loads((DATA/'incoming-818-75-region-replay.json').read_text())
assert region['endpoint_replays']==302 and region['diagram_replays']==4
lp=json.loads((DATA/'incoming-818-75-lp-replay.json').read_text())
assert lp['genuine_completed_certificates_verified']==7 and lp['searches_run']==0 and lp['native_constructors_run']==0
for name,keys in [('anchored-relaxation',['source_cases','anchor_patterns']),
                  ('rooted-tree-envelope',['matrix_entries','literal_mesh_pairs','uniquely_exposed_optima'])]:
    record=json.loads((DATA/f'{name}.json').read_text())
    for p,h in record['source_sha256'].items():assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
    assert [record[k] for k in keys]==([11,374] if name=='anchored-relaxation' else [1365,341,63])

log=(ROOT/'synthesis/report.log').read_text()
assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
assert warnings==[f'{x}pt too wide' for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
aux=(ROOT/'synthesis/report.aux').read_text()
starts={name:int(re.search(r'\\newlabel\{'+label+r'\}\{\{'+str(number)+r'\}\{(\d+)\}',aux).group(1))
    for name,label,number in [('contexts','sec:incoming-contexts',131),('envelopes','sec:minimum-envelopes-native',132)]}
toc=(ROOT/'synthesis/report.toc').read_text()
end=int(re.search(r'\\numberline \{133\}Assessment and recommendations\}\{(\d+)\}',toc).group(1))
assert pages>=530 and 515<=starts['contexts']<starts['envelopes']<end
(DATA/'envelopes-latex.txt').write_text('\n'.join(line.rstrip() for line in log.splitlines()).rstrip()+'\n')
visual=json.loads((DATA/'envelopes-visual-review.json').read_text())
assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
assert visual['inspected_pages']==list(range(starts['contexts'],end+1))
paths=['synthesis/report.pdf','synthesis/report.tex','synthesis/make_tables.py','fast/README.md','reports/README.md',
    'synthesis/README.md','synthesis/incoming_contexts.tex','synthesis/minimum_envelopes.tex',
    'synthesis/minimum_envelopes_results.tex','synthesis/tables/envelopes_enumeration.tex',
    'synthesis/tables/envelopes_discovery.tex','synthesis/data/envelopes_review.py','synthesis/data/envelopes_tables.py',
    'synthesis/data/anchored_relaxation.py','synthesis/data/rooted_tree_envelope.py',
    'synthesis/data/anchored-relaxation.json','synthesis/data/rooted-tree-envelope.json']
paths += [str(p.relative_to(ROOT)) for p in DATA.glob('envelopes-*') if p.name!='envelopes-review.json']
paths += [str(p.relative_to(ROOT)) for p in DATA.glob('incoming-818-*')]
result=dict(runtime_revision='6789f6b73',preserved_reports=list(range(70,76)),source_pins_per_dataset=567,
    maintained_tests=1351,focused_tests=42,eligible_sector_comparisons=9344,automatic_comparisons=9360,
    fresh_regina_full_enumerations=15,producer_disabled_coverage_proofs=70,extra_disc_proofs=1,
    family_ray_lists=9,family_topology_vectors=97,benchmark_measured=260,benchmark_warmups=52,
    active_support_proofs=37,normal_search_proofs=7,batch_proofs=24,sequential_transport_proofs=500,
    trace_replays=217,region_replays=302,genuine_lp_replays=7,regina_trace_states=23,regina_trace_moves=176,
    constructive_relaxation_controls=374,rooted_tree_matrix_entries=1365,
    pdf_pages=pages,section_starts=starts,new_section_pages=list(range(starts['contexts'],end+1)),
    preexisting_overfull_warnings=warnings,sha256={p:sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)})
(DATA/'envelopes-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='sha256'}))
