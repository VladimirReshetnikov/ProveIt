"""Recheck preserved deliveries, sector proofs, native gates and publication."""
from hashlib import sha256
import json
from pathlib import Path
import re
import runpy
import subprocess
import sys
from types import ModuleType

ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_sector_verify import verify_sector_witness,verify_sector_exhaustion
from fastunknot.interval_orbit_verify import verify_orbit_certificate

def load(name):return json.loads((DATA/f'incoming-sectors-{name}.json').read_text())
bench=load('benchmark');audit=load('enumeration-audit');proofs=load('certificate-audit')
assert len(bench['source_sha256'])==700
for p,h in bench['source_sha256'].items():assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
for record in load('placement'):
    for p,h in record['file_sha256'].items():
        assert sha256((ROOT/'reports'/str(record['report'])/p).read_bytes()).hexdigest()==h,p
    assert not (ROOT/'reports'/str(record['report'])/record['omitted'][0]).exists()
for record in load('older-placement'):
    for p,h in record['file_sha256'].items():
        assert sha256((ROOT/'reports'/str(record['report'])/p).read_bytes()).hexdigest()==h,p
    for omitted in record['omitted']:
        assert not (ROOT/'reports'/str(record['report'])/omitted).exists()
assert len(list((ROOT/'reports/59').rglob('*')))>32
assert not (ROOT/'reports/59/SHA256SUMS').exists()
for name in ('normal_sector.py','normal_sector_verify.py'):
    assert (ROOT/'fast/fastunknot'/name).read_bytes()==(ROOT/'reports/57/fast/fastunknot'/name).read_bytes()
assert sha256((ROOT/'fast/fastunknot/normal_sector.py').read_bytes()).hexdigest()==audit['producer_source_sha256']
assert len(audit['records'])==1718
assert all(p['status']=='PASS' for r in audit['records'] for p in r['phases'].values())
assert audit['summary']['quadrilateral_rays_compared']==2361
assert audit['summary']['standard_rays_compared']==3249
corpus=json.loads((ROOT/'reports/57/results/discovery_corpus.json').read_text())
fixtures={r['id']:r['triangulation'] for r in corpus['records']}
assert len(proofs['records'])==962 and len(proofs['mutations'])==60
for record in proofs['records']:
    cert=proofs['certificates'][record['certificate_sha256']]
    verify=verify_sector_witness if record['status']=='DISC_FOUND' else verify_sector_exhaustion
    assert verify(fixtures[record['fixture_id']],cert)
assert all(r['rejected'] for r in proofs['mutations'])
assert load('port-native')['comparisons']==402
assert 'PASS: 250 genuine maintained-kernel integration cases' in (DATA/'incoming-sectors-sparse-port-native.txt').read_text()
transfer=load('transfer-native')
assert len(transfer['cases'])==64 and sum(c['result']['status']=='COMPLETE' for c in transfer['cases'])==12
topology=load('topology-native')
assert topology['all_checks_passed'] and topology['fresh_oracle_recheck']
assert topology['summary']['verified_certificates']==1395 and topology['summary']['cases']==664
assert topology['summary']['triangulation_isomorphism_classes']==26
assert 'Ran 60 tests' in (DATA/'incoming-sectors-overlay-tests.txt').read_text()
for name,count in [('port-tests',25),('transfer-tests',24),('sparse-port-tests',19)]:
    log=(DATA/f'incoming-sectors-{name}.txt').read_text()
    assert f'Ran {count} tests' in log and '\nOK\n' in log
counter=load('reflection-counterexample')
assert verify_orbit_certificate(3,counter['pairings'],counter['incorrect_certificate']['orbit_proof'])
module=ModuleType('_delivered_transversal_checker');module.__package__='fastunknot'
path=ROOT/'reports/58/code/fast/fastunknot/orbit_transversal_verify.py'
exec(compile(path.read_bytes(),str(path),'exec'),module.__dict__)
assert module.verify_orbit_transversal_certificate(3,counter['pairings'],counter['incorrect_certificate'])
assert counter['incorrect_certificate']['representative_intervals']==[[0,2]]
assert counter['actual_minimum_intervals']==[[0,1],[2,3]]
assert not (ROOT/'fast/fastunknot/orbit_transversal_verify.py').exists()
assert bench['measured_calls']==bench['completed_calls']==140 and bench['warmup_calls']==28
runpy.run_path(str(DATA/'incoming_sectors_tables.py'))
assert 'Ran 1269 tests in 229.890s\n\nOK' in (DATA/'incoming-sectors-tests.txt').read_text()
assert 'Ran 8 tests in 0.026s\n\nOK' in (DATA/'incoming-sectors-focused-tests.txt').read_text()
log=(ROOT/'synthesis/report.log').read_text()
assert not re.search(r'undefined|Label\(s\) may have changed',log)
warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
assert warnings==[f'{x}pt too wide' for x in ('12.64871','13.49065','9.04614','35.14671')]
pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
aux=(ROOT/'synthesis/report.aux').read_text()
start=int(re.search(r'\\newlabel\{sec:incoming-sectors\}\{\{126\}\{(\d+)\}',aux).group(1))
toc=(ROOT/'synthesis/report.toc').read_text()
end=int(re.search(r'\\numberline \{127\}Assessment and recommendations\}\{(\d+)\}',toc).group(1))
assert (pages,start,end)==(498,490,495)
(DATA/'incoming-sectors-latex.txt').write_text('\n'.join(line.rstrip() for line in log.splitlines()).rstrip()+'\n')
paths=['synthesis/report.pdf','synthesis/report.tex','synthesis/make_tables.py','fast/README.md','reports/README.md','synthesis/README.md',
       'synthesis/incoming_sectors.tex','synthesis/incoming_sectors_results.tex','synthesis/tables/incoming_sectors_timings.tex']
paths += [str(p.relative_to(ROOT)) for p in DATA.glob('incoming-sectors-*') if not p.name.endswith('review.json')]
paths += ['synthesis/data/incoming_sectors_review.py','synthesis/data/incoming_sectors_tables.py']
result=dict(runtime_revision='5cb112977',preserved_reports=list(range(54,64)),source_pins=700,
    maintained_tests=1269,focused_tests=8,sector_phase_comparisons=3436,sector_certificate_replays=962,
    benchmark_measured=140,benchmark_warmups=28,reflection_counterexample_reproduced=True,
    pdf_pages=pages,section=126,section_pages=list(range(start,end)),preexisting_overfull_warnings=warnings,
    sha256={p:sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)})
(DATA/'incoming-sectors-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='sha256'}))
