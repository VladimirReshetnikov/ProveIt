#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-vars-bd-retry02-terminal-frontier-independent', '0343696c20c2cef50f762fee19d921f489758a0f14b5356e44202296a5e94c2a', '229d0f5d7a49792c6f0e32ea635b31a4c34bcb4174ebfe9b957580e925587862')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-vars-cd-draft'
for n,h in [('Norm38MacroVarsCd', 'fa636d77fbc32142d8aa67c3d556cb970cd536e79a964e57c88a64a538253c79')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-vars-bd-retry02-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroVarsBd', '/tmp/nine-seed38-jones-vars-bd-retry02-20261106/lib/DiophantineConsistency', '04918fb03433f8f26c2cf52f792235c47b4a7e9687dd967182f52a340d64e3f4')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'One audited RingVars/Bd producer; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
