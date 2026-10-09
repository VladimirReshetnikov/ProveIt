"""Recheck the complete weighted-cover release and its retained evidence."""
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

ROOT=Path(__file__).resolve().parents[2];DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_topology_verify import verify_normal_topology_spectrum

audit=json.loads((DATA/'weighted-coorientation-audit.json').read_text())
bench=json.loads((DATA/'weighted-coorientation-benchmark.json').read_text())
repeat=json.loads((DATA/'weighted-coorientation-fallback-benchmark.json').read_text())
regina=json.loads((DATA/'weighted-coorientation-regina.json').read_text())
for record in (audit,bench,repeat):
    assert len(record['source_sha256'])==557
    assert record['source_sha256']==audit['source_sha256']
    for p,h in record['source_sha256'].items():assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
assert repeat['driver_sha256']==sha256((DATA/'weighted_coorientation_fallback.py').read_bytes()).hexdigest()
for p,h in regina['runtime_sources'].items():assert sha256((ROOT/'fast'/p).read_bytes()).hexdigest()==h,p
assert regina['complete'] and regina['all_checks_passed'] and regina['fresh_oracle_recheck']
assert regina['runtime_sources_unchanged'] and not regina['failures']
assert regina['summary']['cases']==664 and regina['summary']['verified_certificates']==1395
assert regina['summary']['triangulation_isomorphism_classes']==26
assert len(audit['cases'])==audit['legacy_exact_comparisons']==5100
assert sum(r['derived'] for r in audit['cases'])==audit['derived']==1088
assert len(audit['examples'])==80
assert all(r['derived'] or (r['old_cycles'],r['old_bytes'])==(r['new_cycles'],r['new_bytes']) for r in audit['cases'])
hashes={};old=None
for name in ('normal_topology','normal_topology_verify'):
    path='Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
    source=subprocess.check_output(['git','show',audit['baseline']+':'+path],cwd=ROOT)
    hashes[name]=sha256(source).hexdigest()
    if name.endswith('verify'):
        old=ModuleType('_weighted_coorientation_review_old');old.__package__='fastunknot'
        exec(compile(source,audit['baseline']+':'+path,'exec'),old.__dict__)
assert all(r['baseline_source_sha256']==hashes for r in (audit,bench,repeat))
disabled=['fastunknot.normal_topology.normal_topology_spectrum',
    'fastunknot.normal_topology.canonical_disk_core','fastunknot.normal_topology.orbit_transversal',
    'fastunknot.normal_topology.weighted_orbit_histogram','fastunknot.normal_surface_parity._parity_certificate',
    'fastunknot.interval_orbits.count_orbits','fastunknot.interval_orbits._count_orbits',
    'fastunknot.topology_spectrum.recover_topology_spectrum','fastunknot.topology_spectrum.scale_core_spectrum']
with ExitStack() as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer called during replay')))
    for row in audit['examples']:
        assert verify_normal_topology_spectrum(row['triangulation'],row['coordinates'],row['certificate'])
        assert verify_normal_topology_spectrum(row['triangulation'],row['coordinates'],row['legacy_certificate'])
        assert old.verify_normal_topology_spectrum(row['triangulation'],row['coordinates'],row['legacy_certificate'])
assert bench['completed_calls']==bench['measured_calls']==300 and bench['warmup_calls']==60
assert repeat['completed_calls']==repeat['measured_calls']==180 and repeat['warmup_calls']==12
for row in repeat['cases']:
    values=[{k:v for k,v in m.items() if k!='seconds'} for s in row['samples']+row['warmups']
            for m in s['measurements'].values()]
    assert all(v['completed'] and v==values[0] for v in values)
runpy.run_path(str(DATA/'weighted_coorientation_tables.py'))
assert 'Ran 1322 tests in 223.502s\n\nOK' in (DATA/'weighted-coorientation-tests.txt').read_text()
assert 'Ran 39 tests in 1.582s\n\nOK' in (DATA/'weighted-coorientation-focused.txt').read_text()
log=(ROOT/'synthesis/report.log').read_text()
assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
assert warnings==[f'{x}pt too wide' for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
aux=(ROOT/'synthesis/report.aux').read_text()
start=int(re.search(r'\\newlabel\{sec:weighted-coorientation\}\{\{130\}\{(\d+)\}',aux).group(1))
toc=(ROOT/'synthesis/report.toc').read_text()
end=int(re.search(r'\\numberline \{131\}Assessment and recommendations\}\{(\d+)\}',toc).group(1))
assert pages>=517 and 510<=start<end
(DATA/'weighted-coorientation-latex.txt').write_text('\n'.join(line.rstrip() for line in log.splitlines()).rstrip()+'\n')
visual=json.loads((DATA/'weighted-coorientation-visual-review.json').read_text())
assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
assert visual['inspected_pages']==list(range(start,end+1))
paths=['synthesis/report.pdf','synthesis/report.tex','synthesis/make_tables.py','fast/README.md','reports/README.md',
    'synthesis/README.md','synthesis/topology_spectra.tex','synthesis/weighted_coorientation.tex',
    'synthesis/weighted_coorientation_results.tex','synthesis/tables/weighted_coorientation_native.tex',
    'synthesis/tables/weighted_coorientation_coordinates.tex','synthesis/data/weighted_coorientation_review.py',
    'synthesis/data/weighted_coorientation_tables.py','synthesis/data/weighted_coorientation_fallback.py']
paths += [str(p.relative_to(ROOT)) for p in DATA.glob('weighted-coorientation-*') if p.name!='weighted-coorientation-review.json']
result=dict(runtime_revision='767de62cc',source_pins_per_dataset=557,maintained_tests=1322,focused_tests=39,
    corpus_configurations=5100,derived_configurations=1088,regina_vectors=664,regina_certificates=1395,
    retained_examples=80,producer_disabled_proofs=160,legacy_checker_replays=80,
    benchmark_measured=300,benchmark_warmups=60,fallback_measured=180,fallback_warmups=12,
    pdf_pages=pages,section=130,section_pages=list(range(start,end+1)),preexisting_overfull_warnings=warnings,
    sha256={p:sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)})
(DATA/'weighted-coorientation-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='sha256'}))
