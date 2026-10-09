"""Recheck direction certificates, source pins, measurements and PDF evidence."""
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
from normal_orbit_research.direction import baseline

audit=json.loads((DATA/'orbit-direction-audit.json').read_text())
bench=json.loads((DATA/'orbit-direction-benchmark.json').read_text())
_,old_hashes=baseline()
for record in (audit,bench):
    assert len(record['source_sha256'])==526
    for path,digest in record['source_sha256'].items():
        assert sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    assert record['baseline_source_sha256']==old_hashes
assert len(audit['configurations'])==10200 and audit['default_exact_comparisons']==5100
assert len(audit['random_comparisons'])==4000 and len(audit['examples'])==56
for row in audit['examples']:
    assert verify_normal_surface_certificate(row['triangulation'],row['coordinates'],row['certificate'])
counter=audit['counterexample']
for key in ('old','new'):
    assert verify_normal_surface_certificate(counter['triangulation'],counter['coordinates'],counter[key])
assert (counter['old_metrics']['cycles'],counter['new_metrics']['cycles'])==(45,41)
assert (counter['old_metrics']['events'],counter['new_metrics']['events'])==(421,621)
assert bench['completed_calls']==bench['measured_calls']==240 and bench['warmup_calls']==48
runpy.run_path(str(DATA/'orbit_direction_tables.py'))
assert 'Ran 1255 tests in 223.960s\n\nOK' in (DATA/'orbit-direction-tests.txt').read_text()
assert 'Ran 29 tests in 1.868s\n\nOK' in (DATA/'orbit-direction-focused-tests.txt').read_text()
log=(ROOT/'synthesis/report.log').read_text()
assert not re.search(r'undefined|Label\(s\) may have changed',log)
warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
assert warnings==[f'{x}pt too wide' for x in ('12.64871','13.49065','9.04614','35.14671')]
pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
aux=(ROOT/'synthesis/report.aux').read_text()
start=int(re.search(r'\\newlabel\{sec:orbit-direction\}\{\{124\}\{(\d+)\}',aux).group(1))
toc=(ROOT/'synthesis/report.toc').read_text()
end=int(re.search(r'\\numberline \{125\}Assessment and recommendations\}\{(\d+)\}',toc).group(1))
assert (pages,start,end)==(490,483,487)
(DATA/'orbit-direction-latex.txt').write_text('\n'.join(line.rstrip() for line in log.splitlines()).rstrip()+'\n')
paths=['synthesis/report.pdf','synthesis/report.tex','synthesis/make_tables.py','fast/README.md','synthesis/README.md',
       'synthesis/orbit_direction.tex','synthesis/orbit_direction_results.tex',
       'synthesis/tables/orbit_direction_counts.tex','synthesis/tables/orbit_direction_timings.tex']
paths += [str(p.relative_to(ROOT)) for p in DATA.glob('orbit-direction-*') if not p.name.endswith('review.json')]
paths += ['synthesis/data/orbit_direction_review.py','synthesis/data/orbit_direction_tables.py']
runtime=subprocess.check_output(['git','log','-1','--format=%H','--',str(ROOT/'fast/fastunknot/interval_orbits.py')],cwd=ROOT).decode().strip()
result=dict(runtime_revision=runtime,source_pins_per_dataset=526,maintained_tests=1255,focused_tests=29,
            default_exact_comparisons=5100,normal_direction_comparisons=10200,literal_interval_comparisons=4000,
            retained_proofs_replayed=58,benchmark_measured=240,benchmark_warmups=48,
            measured_surface_calls=25720,warmup_surface_calls=5144,
            pdf_pages=pages,section=124,section_pages=list(range(start,end)),
            preexisting_overfull_warnings=warnings,
            sha256={p:sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)})
(DATA/'orbit-direction-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='sha256'}))
