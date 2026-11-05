#!/usr/bin/env python3
"""Read-only frozen probe verification; does not invoke Lean."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('Use python3 -I -S -B')
def need(b,s):
 if not b:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
here=Path(__file__).resolve().parent
pins={'runner-captured.py':'c1d08e82d6a0b1a670e756b3eaddf9821f27cfbd1a0f66ae35d1e3bda77115cc',
 'result.json':'914339a67b5a866cb577de5e12b79a0212cb725c4307ae87c699e539efefe20d',
 'trace.py':'b8bfb62a29f6cd3868a101c8e3c13036a1d982aa568f5182d8b600e8e9f72e3f',
 'trace-result.json':'d26955072436cf2c337f084a3572297b61250591fd62d6a5fd9d4da7aada02e9',
 'outer-observation.json':'0cc95b049b663cd97f63dfc7c75401bd3f8a24da6704d8257f6347d2b1eabc33'}
for name,h in pins.items():need(sha(here/name)==h,'pin '+name)
r=json.loads((here/'result.json').read_text());o=json.loads((here/'outer-observation.json').read_text())
need(r['status']=='COMPLETED_BOTH' and r['runner_sha256']==pins['runner-captured.py'] and o['observed_runner_exit']==0 and o['result_sha256']==pins['result.json'],'runner status')
need([x['case'] for x in r['results']]==['foundation_first','mathlib_first'],'case order')
for x in r['results']:
 d=here/x['case'];src=d/'Probe.lean';out=d/'stdout.log';err=d/'stderr.log'
 need(x['exit']==1 and x['monitor_failure'] is None and x['object_sha256'] is None and x['events']==[],'Lean result')
 need(sha(src)==x['source_sha256'] and sha(out)==x['stdout_sha256'] and sha(err)==x['stderr_sha256'] and not err.read_bytes(),'captured source/log')
 need(src.read_text()==''.join('import '+m+'\n' for m in x['imports']),'source imports')
 q=x['owned_receipt'];pid=q['pid'];need(q['exit']==1 and q['session_drained'] and q['direct_child_reaped'] and q['initial']['pgrp']==q['initial']['session']==pid,'owned receipt')
 need(not (d/'Probe.olean').exists(),'unexpected object')
text1=(here/'foundation_first/stdout.log').read_text();text2=(here/'mathlib_first/stdout.log').read_text()
need("import Mathlib.LinearAlgebra.Matrix.Defs failed" in text1 and "already contains 'Matrix.map' from Foundation.Vorspiel.Matrix" in text1,'foundation-first diagnostic')
need("import Foundation.Vorspiel.Matrix failed" in text2 and "already contains 'Matrix.map.eq_1' from Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber" in text2,'mathlib-first diagnostic')
for name,entry in r['provider_guards'].items():
 p=Path(name)
 if entry is None:need(not os.path.lexists(p),'new companion '+name)
 else:need(p.is_file() and str(p.resolve())==entry['realpath'] and sha(p)==entry['sha256'],'provider drift '+name)
t=subprocess.run([sys.executable,'-I','-S','-B',str(here/'trace.py')],capture_output=True,check=True,timeout=20)
need(t.stdout==(here/'trace-result.json').read_bytes() and not t.stderr,'source trace drift')
out={'status':'PASS_CAPTURED_DIAGNOSTICS','script_sha256':sha(__file__),'runner_result_sha256':pins['result.json'],
     'trace_result_sha256':pins['trace-result.json'],'outer_observation_sha256':pins['outer-observation.json'],
     'foundation_first_lean_exit':1,'mathlib_first_lean_exit':1,
     'scope':'Two captured import failures and current source-edge trace; no Lean replay, endpoint conclusion or full transitive provenance.'}
print(json.dumps(out,indent=2,sort_keys=True))
