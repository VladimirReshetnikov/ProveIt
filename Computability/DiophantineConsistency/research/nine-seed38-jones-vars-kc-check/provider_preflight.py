#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-vars-wt-terminal-frontier-independent', 'b6bc0768593b3e30b0527049fffce56cb585e6fdb1e86d1a0d8c8bc35d696976', 'dd7af379ed2bd7118708b761cad90fa36151597a1488c68c07fa9c53f18a4306')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-vars-kc-draft'
for n,h in [('Norm38MacroVarsDm', 'eee78f45150d3b4f47ff6723fe76daf2226db330e62512941cb300a0d7fc339c'), ('Norm38MacroVarsKc', '9b4bddfa3add30f4502b242af00f4c56f23ad6e9639e80a08009f891b513a491')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-vars-wt-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroVarsWt1', '/tmp/nine-seed38-jones-vars-wt-check-20261106/lib/DiophantineConsistency', 'c1317d8835be2a9775fda42b676fb4f117206ef456bcd57af9fa53df1dd32347')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'One audited RingVars weight producer; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
