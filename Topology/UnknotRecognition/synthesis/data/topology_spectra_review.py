"""Recheck source pins, complete spectra, trace guards, timings and publication."""
from contextlib import ExitStack
from hashlib import sha256
import json
from pathlib import Path
import re
import runpy
import sys
from types import ModuleType
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_topology_verify import verify_normal_topology_spectrum
from fastunknot.orbit_transversal_verify import verify_orbit_transversal_certificate
from fastunknot.interval_orbit_verify import verify_orbit_certificate
from fastunknot.orbit_transversal import orbit_transversal
from fastunknot.interval_orbits import IntervalPairing

audit=json.loads((DATA/'topology-spectra-audit.json').read_text())
bench=json.loads((DATA/'topology-spectra-benchmark.json').read_text())
regina=json.loads((DATA/'topology-spectra-regina.json').read_text())
for record in (audit,bench):
    assert len(record['source_sha256'])==551
    for p,h in record['source_sha256'].items():assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
for p,h in regina['runtime_sources'].items():assert sha256((ROOT/'fast'/p).read_bytes()).hexdigest()==h,p
assert audit['configurations']==len(audit['cases'])==5100
assert audit['input_vectors']==1275 and len(audit['examples'])==56
assert regina['complete'] and regina['all_checks_passed'] and regina['fresh_oracle_recheck']
assert not regina['failures'] and regina['runtime_sources_unchanged']
assert regina['summary']['cases']==664 and regina['summary']['verified_certificates']==1395
assert regina['summary']['triangulation_isomorphism_classes']==26
disabled=['fastunknot.normal_topology.normal_topology_spectrum',
    'fastunknot.interval_orbits.count_orbits','fastunknot.interval_orbits._count_orbits',
    'fastunknot.orbit_transversal._forward_selector','fastunknot.weighted_orbits.weighted_orbit_histogram',
    'fastunknot.topology_spectrum.recover_topology_spectrum','fastunknot.topology_spectrum.scale_core_spectrum',
    'fastunknot.normal_disk_kernel.canonical_disk_core','fastunknot.normal_topology_geometry.spectrum_summary']
with ExitStack() as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer called during replay')))
    for row in audit['examples']:
        assert verify_normal_topology_spectrum(row['triangulation'],row['coordinates'],row['certificate'])
counter=json.loads((DATA/'incoming-sectors-reflection-counterexample.json').read_text())
source=counter['pairings'];cert=counter['incorrect_certificate']
assert verify_orbit_certificate(3,source,cert['orbit_proof'])
assert not verify_orbit_transversal_certificate(3,source,cert)
old=ModuleType('_historical_transversal_checker');old.__package__='fastunknot'
path=ROOT/'reports/58/code/fast/fastunknot/orbit_transversal_verify.py'
exec(compile(path.read_bytes(),str(path),'exec'),old.__dict__)
assert old.verify_orbit_transversal_certificate(3,source,cert)
fixed=orbit_transversal(3,[IntervalPairing(0,0,1,1)],record_certificate=True)
assert fixed['representative_intervals']==[[0,1],[2,3]]
assert verify_orbit_transversal_certificate(3,source,fixed['certificate'])
assert bench['completed_calls']==bench['measured_calls']==300 and bench['warmup_calls']==60
runpy.run_path(str(DATA/'topology_spectra_tables.py'))
assert 'Ran 1312 tests in 222.203s\n\nOK' in (DATA/'topology-spectra-tests.txt').read_text()
assert 'Ran 43 tests in 1.569s\n\nOK' in (DATA/'topology-spectra-focused-tests.txt').read_text()
log=(ROOT/'synthesis/report.log').read_text()
assert not re.search(r'undefined|Label\(s\) may have changed',log)
warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
assert warnings==[f'{x}pt too wide' for x in ('12.64871','13.49065','9.04614','35.14671')]
pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
aux=(ROOT/'synthesis/report.aux').read_text()
start=int(re.search(r'\\newlabel\{sec:topology-spectra-native\}\{\{127\}\{(\d+)\}',aux).group(1))
toc=(ROOT/'synthesis/report.toc').read_text()
end=int(re.search(r'\\numberline \{128\}Assessment and recommendations\}\{(\d+)\}',toc).group(1))
assert (pages,start,end)==(503,496,500)
(DATA/'topology-spectra-latex.txt').write_text('\n'.join(line.rstrip() for line in log.splitlines()).rstrip()+'\n')
paths=['synthesis/report.pdf','synthesis/report.tex','synthesis/make_tables.py','fast/README.md','reports/README.md','synthesis/README.md',
       'synthesis/topology_spectra.tex','synthesis/topology_spectra_results.tex','synthesis/incoming_sectors.tex',
       'synthesis/tables/topology_spectra_coordinates.tex','synthesis/tables/topology_spectra_core.tex']
paths += [str(p.relative_to(ROOT)) for p in DATA.glob('topology-spectra-*') if not p.name.endswith('review.json')]
paths += ['synthesis/data/topology_spectra_review.py','synthesis/data/topology_spectra_tables.py']
result=dict(runtime_revision='bbebe9c39',source_pins_per_dataset=551,maintained_tests=1312,focused_tests=43,
    full_type_comparisons=5100,regina_vectors=664,regina_certificates=1395,
    producer_disabled_retained_proofs=56,reflection_counterexample_rejected=True,
    benchmark_measured=300,benchmark_warmups=60,pdf_pages=pages,section=127,section_pages=list(range(start,end+1)),
    preexisting_overfull_warnings=warnings,sha256={p:sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)})
(DATA/'topology-spectra-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='sha256'}))
