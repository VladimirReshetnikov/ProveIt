"""Focused imaginary-sentinel equivalence and failure controls."""
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile
ROOT=Path(__file__).resolve().parents[1]
candidate=ROOT/'code/checker_bytes.py'
source=candidate.read_text()
values=[None,False,True,0,1,-1,0.0,-0.0,0.5,-0.5,float('nan'),float('inf'),-float('inf'),'','x',[],[0],[0,1],{}, {'x':0}]
comparisons=0
for m,s,u,t in itertools.product(values,repeat=4):
    old=bool(m) and m in ([s,u],not s and[t]*3)
    new=m in ([s,u],s and 1j or[t]*3)
    if bool(old)!=bool(new):raise ValueError((m,s,u,t))
    comparisons+=1
one=[0]
C=[[one],one,0]
false_target=[one,0]
wrong_match_packet=[[0,one,one,0],[0,C,one,[3,0]],false_target]
missing_image_packet=[[0,0,3,0],[[0,3,0],-1]]
mutations={
    'unguarded_false_disabled_marker':source.replace('s and 1j or [t] * 3','not s and [t] * 3'),
    'missing_image_silently_zero':source.replace('t=0j','t=0'),
}
cases=[('false_disabled_marker',wrong_match_packet,'unguarded_false_disabled_marker'),('missing_image',missing_image_packet,'missing_image_silently_zero')]
results=[]
with tempfile.TemporaryDirectory() as d:
    for name,packet,mutation in cases:
        mutant=Path(d)/(mutation+'.py');mutant.write_text(mutations[mutation])
        for path,expected in [(candidate,False),(mutant,True)]:
            for optimized in (False,True):
                run=subprocess.run([sys.executable]+(['-O'] if optimized else[])+[str(path)],input=json.dumps(packet),text=True,capture_output=True,timeout=10)
                accepted=run.returncode==0 and run.stdout=='ACCEPT\n'
                results.append(dict(name=name,implementation='correct' if path==candidate else mutation,optimized=optimized,expected=expected,actual=accepted,passed=accepted==expected,stderr=run.stderr[-800:] if accepted!=expected else''))
output=dict(finite_boolean_comparisons=comparisons,control_packets={name:packet for name,packet,_ in cases},checks=len(results),failures=[x for x in results if not x['passed']],results=results,qualification='The missing-image control is an invalid closed goal with an unallocated free name; the disabled-marker control has the genuine false closed goal 1=0.')
(ROOT/'evidence/sentinel_receipt.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps({k:v for k,v in output.items() if k not in ('results','control_packets')},indent=2))

if output["failures"]: raise SystemExit(1)
