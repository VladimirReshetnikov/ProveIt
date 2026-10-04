"""Fresh read-only receipt for a bounded knot-report interface review.

No archived/committed program is executed, imported, or reconstructed.
"""
from pathlib import Path
import hashlib, json, subprocess

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
REV='78333302d9babf0efb1a5d218e122f13c35bb306'
BASE='Topology/UnknotRecognition/'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(ROOT),*args])
def record(path,spans):
    data=git('show',REV+':'+path); lines=data.splitlines(keepends=True)
    result={'path':path,'blob':git('rev-parse',REV+':'+path).decode().strip(), 'bytes':len(data),'sha256':sha(data),'lines':len(lines),'read_spans':[]}
    for lo,hi in spans:
        if hi is None:hi=len(lines)
        if not 1<=lo<=hi<=len(lines):raise ValueError((path,lo,hi))
        b=b''.join(lines[lo-1:hi]);result['read_spans'].append({'first':lo,'last':hi,'bytes':len(b),'sha256':sha(b)})
    return result
records=[record(BASE+'README.md',[(1,None)]),record(BASE+'synthesis/README.md',[(1,None)]),record(BASE+'synthesis/report.tex',[(1,240),(384,433),(489,525),(580,612)])]
for rec in records:
    if sha((ROOT/rec['path']).read_bytes())!=rec['sha256']:raise ValueError('working read differs from immutable input')
result={'revision':REV,'parent':git('rev-parse',REV+'^').decode().strip(),'records':records,'read_line_total':sum(s['last']-s['first']+1 for r in records for s in r['read_spans']),
 'scope':{'read_guides':2,'selected_report_spans':4,'complete_report_read':False,'source_implementation_read':False,'archive_inventory':False,'external_source_verification':False,'builds_or_predecessor_execution':False},'collector_sha256':sha(Path(__file__).read_bytes())}
Path('/tmp/review_unknot_interface_78333302d.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'read_line_total':result['read_line_total'],'records':len(records),'receipt_sha256':sha(Path('/tmp/review_unknot_interface_78333302d.json').read_bytes())}))
