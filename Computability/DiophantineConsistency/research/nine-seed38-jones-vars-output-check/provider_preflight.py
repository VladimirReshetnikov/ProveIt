#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-vars-kc-terminal-frontier-independent', '04d574b60ac7d52000d1462770e38d57e9d37c71c84cb918d34d382d714ffffe', 'e6f9a56c3ecf0af27a2921f63d7b866b32be2e2938492bec7e43924fc7d4d98d')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-vars-output-draft'
for n,h in [('Norm38MacroVarsOutput', '4d1240af3ed3a10a9dcc4244e7aa07836816a8bcca632f315a4789a37e6f8f12')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-vars-kc-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroVarsKc', '/tmp/nine-seed38-jones-vars-kc-check-20261106/lib/DiophantineConsistency', 'cb7a316ae929ac862636d460e7b8da8be066cfd23555be8ee3958f0b0ce4e041')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'One audited RingVars margin/Kc producer; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
