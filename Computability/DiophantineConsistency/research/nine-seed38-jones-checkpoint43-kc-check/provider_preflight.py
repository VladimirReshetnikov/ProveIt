#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-checkpoint42-dm-terminal-frontier-independent', '38692c3d7cc34e2a0e02d9737f54519db03d190cfe9bcaf907b3d15871770cb4', '2846d0959266f652a6e9da93fff87b6e72adaced0e2004e1d05d961a73db7137')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint43-kc-draft'
for n,h in [('Norm38MacroKcValue', 'c754b51cffbadef259c6c2a6196a704d84909cb8b80850261abf14ae270d005b')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint42-dm-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroDmValue', '/tmp/nine-seed38-jones-checkpoint42-dm-check-20261106/lib/DiophantineConsistency', 'd7e21e6b765a1a796c0f87165394188f19bc25df619a32fd7d9d8780948c803a')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'One audited Dm producer; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
