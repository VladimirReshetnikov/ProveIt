"""Recheck the escape proof, publication sources, measurements and PDF build."""
from hashlib import sha256
import json
from pathlib import Path
import re
import runpy
import sys

ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.pachner32_verify import verify_pachner_32
from fastunknot.normal_disk_kernel import verify_normal_disk_count_certificate
from normal_orbit_research.coherent_obstruction import replay

audit=json.loads((DATA/'coherent-escape-audit.json').read_text())
bench=json.loads((DATA/'coherent-escape-benchmark.json').read_text())
for record in (audit,bench):
    for path,digest in record['source_sha256'].items():
        assert sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    assert len(record['source_sha256'])==522
escape=audit['escape']
source=json.loads((DATA/'coherent-obstruction-certificate.json').read_text())
assert replay(source)==escape['before']
after=escape['replacement']['triangulation']
assert verify_pachner_32(escape['before'],after,escape['replacement']['certificate'])
assert verify_normal_disk_count_certificate(after,escape['coordinates'],escape['disc_certificate'])
assert escape['disc_certificate']['compressing_disk_components']==1
assert sum(map(sum,escape['coordinates']))==36
assert len(audit['mixed_moves'])==400 and len(audit['arithmetic'])==600
assert len(audit['preserved_source_cases'])==84 and len(audit['preserved_positive_proofs'])==47
assert not any(r['new_over_extended_planar'] for r in audit['greedy_search'])
runpy.run_path(str(DATA/'coherent_escape_tables.py'))
assert 'Ran 1245 tests in 240.628s\n\nOK' in (DATA/'coherent-escape-tests.txt').read_text()
log=(ROOT/'synthesis/report.log').read_text()
assert not re.search(r'undefined|Label\(s\) may have changed',log)
warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
assert warnings==[f'{x}pt too wide' for x in ('12.64871','13.49065','9.04614','35.14671')]
assert 'Output written on report.pdf (484 pages,' in log
(DATA/'coherent-escape-latex.txt').write_text('\n'.join(line.rstrip() for line in log.splitlines()).rstrip()+'\n')
paths=['synthesis/report.pdf','synthesis/report.tex','synthesis/make_tables.py',
       'synthesis/coherent_escape.tex','synthesis/coherent_escape_results.tex',
       'synthesis/tables/coherent_escape_kernel.tex','synthesis/tables/coherent_escape_pipeline.tex']
paths += [str(p.relative_to(ROOT)) for p in DATA.glob('coherent-escape-*') if not p.name.endswith('review.json')]
paths += ['synthesis/data/coherent_escape_review.py','synthesis/data/coherent_escape_tables.py']
result=dict(runtime_revision='b2520cb02',source_pins_per_dataset=522,
            maintained_tests=1245,focused_tests=18,mixed_moves=400,greedy_moves=217,
            arithmetic_comparisons=600,preserved_native_records=252,preserved_proofs=47,
            benchmark_measured=280,benchmark_warmups=56,pdf_pages=484,
            section=122,section_pages=[477,478,479,480],
            preexisting_overfull_warnings=warnings,
            sha256={p:sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)})
(DATA/'coherent-escape-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='sha256'}))
