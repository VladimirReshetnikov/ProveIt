#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-terminal-cut-retry01-terminal-frontier-independent', '2fcd5249560ed9f36936ab4f3fe48b694fadd3cb88ed9827cd5ec0bc230f5db9', '19989ca3859a81861e9aaf05a111fd94c09c00b447465d5f796b98cd2c6981cb')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-vars-bd-retry01-draft'
for n,h in [('Norm38MacroVarsBd', '013fdb21287af30502ab6d80f3690b8851ff8732215a6d5f580e6e9b941e982e')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-terminal-cut-retry01-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroTerminalOutput', '/tmp/nine-seed38-jones-terminal-cut-retry01-20261106/lib/DiophantineConsistency', 'd1362486f746e9dfeba1b94ae27f6bb770d8f15ed216fdcf2467f9a08a4bd474')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'One audited terminal-cut producer; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
