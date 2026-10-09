"""Recheck bounded-race sources, retained proofs, bounds and publication."""
from hashlib import sha256
import json
from pathlib import Path
import re
import runpy
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from fastunknot.interval_orbit_verify import verify_orbit_certificate
from fastunknot.interval_orbits import IntervalPairing
from normal_orbit_research import direction, race

audit=json.loads((DATA/'orbit-race-audit.json').read_text())
bench=json.loads((DATA/'orbit-race-benchmark.json').read_text())
_,old_hashes=direction.baseline(race.BASELINE)
for record in (audit,bench):
    assert len(record['source_sha256'])==529
    for path,digest in record['source_sha256'].items():
        assert sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    assert record['baseline_source_sha256']==old_hashes
assert len(audit['normal_cases'])==5100 and audit['normal_restarts']==2972
assert len(audit['interval_cases'])==1210 and audit['legacy_interval_comparisons']==3630
assert len(audit['examples'])==46 and len(audit['fixtures'])==10
for row in audit['examples']:
    assert verify_normal_surface_certificate(row['triangulation'],row['coordinates'],row['certificate'])
for row in audit['fixtures']:
    pairs=[IntervalPairing(*p) for p in row['pairings']]
    assert verify_orbit_certificate(row['size'],pairs,row['certificate'])
for row in audit['interval_cases']:
    s=row['stats'];optimum=min(row['fixed_work']);initial=s['race_initial_allowance'];budget=initial;rounds=0
    while budget<optimum:budget*=2;rounds+=1
    assert budget==s['race_final_allowance']
    assert row['attempt_bound']==4*budget-2*initial+2*rounds+1
    assert s['race_checkpoint_work']<=row['attempt_bound']<=12*max(initial,optimum)
    assert row['actual_checkpoint_work']==s['race_checkpoint_work']+s['race_startup_work']
    assert row['cycles']==s['race_forward_cycles']+s['race_reverse_cycles']
assert bench['completed_calls']==bench['measured_calls']==280 and bench['warmup_calls']==56
runpy.run_path(str(DATA/'orbit_race_tables.py'))
assert 'Ran 1261 tests in 215.994s\n\nOK' in (DATA/'orbit-race-tests.txt').read_text()
assert 'Ran 16 tests in 1.521s\n\nOK' in (DATA/'orbit-race-focused-tests.txt').read_text()
log=(ROOT/'synthesis/report.log').read_text()
assert not re.search(r'undefined|Label\(s\) may have changed',log)
warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
assert warnings==[f'{x}pt too wide' for x in ('12.64871','13.49065','9.04614','35.14671')]
pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
aux=(ROOT/'synthesis/report.aux').read_text()
start=int(re.search(r'\\newlabel\{sec:orbit-race\}\{\{125\}\{(\d+)\}',aux).group(1))
toc=(ROOT/'synthesis/report.toc').read_text()
end=int(re.search(r'\\numberline \{126\}Assessment and recommendations\}\{(\d+)\}',toc).group(1))
assert (pages,start,end)==(493,487,490)
(DATA/'orbit-race-latex.txt').write_text('\n'.join(line.rstrip() for line in log.splitlines()).rstrip()+'\n')
paths=['synthesis/report.pdf','synthesis/report.tex','synthesis/make_tables.py','fast/README.md','synthesis/README.md',
       'synthesis/orbit_race.tex','synthesis/orbit_race_results.tex',
       'synthesis/tables/orbit_race_counts.tex','synthesis/tables/orbit_race_forward.tex','synthesis/tables/orbit_race_wide.tex']
paths += [str(p.relative_to(ROOT)) for p in DATA.glob('orbit-race-*') if not p.name.endswith('review.json')]
paths += ['synthesis/data/orbit_race_review.py','synthesis/data/orbit_race_tables.py']
runtime=subprocess.check_output(['git','log','-1','--format=%H','--',str(ROOT/'fast/fastunknot/interval_race.py')],cwd=ROOT).decode().strip()
assert runtime
result=dict(runtime_revision=runtime,source_pins_per_dataset=529,maintained_tests=1261,focused_tests=16,
            default_exact_surface_comparisons=5100,race_surface_comparisons=5100,
            legacy_interval_comparisons=3630,literal_interval_and_bound_comparisons=1210,
            retained_proofs_replayed=56,benchmark_measured=280,benchmark_warmups=56,
            measured_surface_calls=51200,warmup_surface_calls=10240,measured_kernel_calls=40,warmup_kernel_calls=8,
            pdf_pages=pages,section=125,section_pages=list(range(start,end+1)),
            preexisting_overfull_warnings=warnings,
            sha256={p:sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)})
(DATA/'orbit-race-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='sha256'}))
