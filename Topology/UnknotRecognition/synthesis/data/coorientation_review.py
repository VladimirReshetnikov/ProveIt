"""Recheck retained coorientation proofs, source pins, tables and publication."""
from hashlib import sha256
import json
from pathlib import Path
import re
import runpy
import sys

ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from normal_orbit_research.coorientation import baseline

records=[json.loads((DATA/f'{name}.json').read_text()) for name in (
    'coorientation-audit','coorientation-benchmark','coorientation-corpus-benchmark')]
audit,bench,batch=records
_,_,old_hashes=baseline()
for record,count in zip(records,(524,524,525)):
    assert len(record['source_sha256'])==count
    for path,digest in record['source_sha256'].items():
        assert sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    assert record['baseline_source_sha256']==old_hashes
assert len(audit['cases'])==5100 and audit['derived']==956
assert audit['regina_comparisons']==1275 and audit['triangulations']==45
assert audit['legacy_exact_comparisons']==5100
assert sum(r['derived'] for r in audit['cases'])==956
assert len(audit['examples'])==84
for row in audit['examples']:
    assert verify_normal_surface_certificate(row['triangulation'],row['coordinates'],row['certificate'])
assert bench['completed_calls']==bench['measured_calls']==240 and bench['warmup_calls']==48
assert batch['completed_calls']==batch['measured_calls']==20 and batch['warmup_calls']==4
assert batch['measured_surface_calls']==25500 and batch['warmup_surface_calls']==5100
assert audit['layered_family'][-1]==dict(tetrahedra=256,old_cycles=781,new_cycles=520,
    old_events=166438,new_events=83478,sign_entries=258,old_bytes=14185011,new_bytes=7114254)
runpy.run_path(str(DATA/'coorientation_tables.py'))
assert 'Ran 1250 tests in 219.111s\n\nOK' in (DATA/'coorientation-tests.txt').read_text()
assert 'Ran 46 tests in 2.457s\n\nOK' in (DATA/'coorientation-focused-tests.txt').read_text()
log=(ROOT/'synthesis/report.log').read_text()
assert not re.search(r'undefined|Label\(s\) may have changed',log)
warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
assert warnings==[f'{x}pt too wide' for x in ('12.64871','13.49065','9.04614','35.14671')]
assert 'Output written on report.pdf (487 pages,' in log
assert r'\newlabel{sec:normal-coorientation}{{123}{480}' in (ROOT/'synthesis/report.aux').read_text()
(DATA/'coorientation-latex.txt').write_text('\n'.join(line.rstrip() for line in log.splitlines()).rstrip()+'\n')
paths=['synthesis/report.pdf','synthesis/report.tex','synthesis/make_tables.py','fast/README.md','synthesis/README.md',
       'synthesis/coorientation.tex','synthesis/coorientation_results.tex',
       'synthesis/tables/coorientation_counts.tex','synthesis/tables/coorientation_timings.tex']
paths += [str(p.relative_to(ROOT)) for p in DATA.glob('coorientation-*') if not p.name.endswith('review.json')]
paths += ['synthesis/data/coorientation_review.py','synthesis/data/coorientation_tables.py',
          'synthesis/data/coorientation_corpus_benchmark.py']
result=dict(runtime_revision='3ab606497',source_pins_per_dataset=[524,524,525],
            maintained_tests=1250,focused_tests=46,configurations=5100,derived_configurations=956,
            regina_comparisons=1275,retained_proofs_replayed=84,
            benchmark_measured=240,benchmark_warmups=48,
            batch_measured_surfaces=25500,batch_warmup_surfaces=5100,
            pdf_pages=487,section=123,section_pages=[480,481,482,483],
            preexisting_overfull_warnings=warnings,
            sha256={p:sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)})
(DATA/'coorientation-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='sha256'}))
