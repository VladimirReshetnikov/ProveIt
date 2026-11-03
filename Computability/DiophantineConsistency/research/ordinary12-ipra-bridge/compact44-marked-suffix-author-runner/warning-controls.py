#!/usr/bin/env python3
"""No-Lean controls for the narrowly matched historical warning policy."""
import hashlib,importlib.util,json,tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('runner',HERE/'replay.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
if not __debug__:raise ValueError('optimized Python rejected')
base=m.warning_baseline();src=Path('/tmp/example/ArithmeticWangPlane.lean');text=base.replace('<SOURCE>',str(src))
cases={}
def check(label,fn,expect):
 try:fn();accepted=True
 except Exception:accepted=False
 if accepted!=expect:raise ValueError((label,accepted,expect))
 cases[label]=accepted
check('exact_baseline',lambda:m.accepted_diagnostics(m.PLANE,src,m.PLANE_SHA,text,base),True)
check('wrong_module',lambda:m.accepted_diagnostics('Other',src,m.PLANE_SHA,text,base),False)
check('wrong_source_sha',lambda:m.accepted_diagnostics(m.PLANE,src,'0'*64,text,base),False)
check('wrong_source_path',lambda:m.accepted_diagnostics(m.PLANE,src,m.PLANE_SHA,text.replace(str(src),'/tmp/other.lean'),base),False)
check('changed_warning',lambda:m.accepted_diagnostics(m.PLANE,src,m.PLANE_SHA,text.replace('252:24','252:25'),base),False)
check('missing_warning',lambda:m.accepted_diagnostics(m.PLANE,src,m.PLANE_SHA,text.splitlines()[0]+'\n',base),False)
check('extra_warning',lambda:m.accepted_diagnostics(m.PLANE,src,m.PLANE_SHA,text+text,base),False)
check('extra_output',lambda:m.accepted_diagnostics(m.PLANE,src,m.PLANE_SHA,text+'noise\n',base),False)
check('error',lambda:m.accepted_diagnostics(m.PLANE,src,m.PLANE_SHA,text+'error: injected\n',base),False)
check('sorryAx',lambda:m.accepted_diagnostics(m.PLANE,src,m.PLANE_SHA,text+'sorryAx\n',base),False)
with tempfile.TemporaryDirectory(prefix='warning-baseline-') as d:
 old=m.HIST;m.HIST=Path(d);(m.HIST/'logs').mkdir();(m.HIST/'state.json').write_bytes((old/'state.json').read_bytes());(m.HIST/'logs/DiophantineConsistency_ArithmeticWangPlane-attempt-1.log').write_bytes((old/'logs/DiophantineConsistency_ArithmeticWangPlane-attempt-1.log').read_bytes());(m.HIST/'state.json').write_text('changed')
 check('historical_state_drift',m.warning_baseline,False)
 (m.HIST/'state.json').write_bytes((old/'state.json').read_bytes());(m.HIST/'logs/DiophantineConsistency_ArithmeticWangPlane-attempt-1.log').write_text('changed')
 check('historical_log_drift',m.warning_baseline,False)
print(json.dumps({'status':'PASS_NO_LEAN_WARNING_CONTROLS','runner_sha256':hashlib.sha256((HERE/'replay.py').read_bytes()).hexdigest(),'cases':cases,'lean_launched':False},indent=2,sort_keys=True))
