"""Replay the saved group-stage proofs to record deterministic arena costs."""
from pathlib import Path
from hashlib import sha256
import json
import sys
import tempfile
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]/'fast';sys.path.insert(0,str(ROOT))
from primitive_power_research import forests as harness
from fastunknot import Diagram
from fastunknot.group_certificate import verify_group_certificate
BASELINE='06fcb7685da7770b1f7e9ff1df7f6164222100ee'
harness.BASELINE=BASELINE
source=HERE/'ordered-batch-stages.json';data=json.loads(source.read_text());rows=[]
with tempfile.TemporaryDirectory(prefix='unknot-ordered-replay-work-') as directory:
    old,search,group,hashes=harness.baseline(directory)
    for r in data['cases']:
        cases={}
        for producer in ('old','current'):
            key=r['samples'][0]['measurements'][producer]['groups'][0]['certificate_sha256'];c=data['certificates'][key]
            results={}
            for name,diagram,verify in (('old',old.Diagram,group.verify_group_certificate),('current',Diagram,verify_group_certificate)):
                stats={};assert verify(diagram.from_pd(r['source']['pd']),c,compressed=True,max_work=20000000,stats=stats)
                results[name]=stats
            cases[producer]=dict(certificate_sha256=key,verification_stats=results)
        rows.append(dict(crossings=r['source']['crossings'],cases=cases))
result=dict(cases=rows,source_sha256=sha256(source.read_bytes()).hexdigest(),driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),baseline_commit=BASELINE,baseline_source_sha256=hashes,native_source_sha256={str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest() for p in (ROOT/'fastunknot').rglob('*.py')},replays=24,scope='Deterministic compressed arena costs after independent source reconstruction; stats.work excludes the preceding diagram-recovery budget. Source and full proof verification still execute. No timings.')
(HERE/'ordered-batch-replay-work.json').write_text(json.dumps(result,indent=2)+'\n')
for r in rows:print(r['crossings'],{k:v['work'] for k,v in r['cases']['current']['verification_stats'].items()})
