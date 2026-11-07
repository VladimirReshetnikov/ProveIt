#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-vars-output-terminal-frontier-independent', '3b400e3ad10bcc957109fe78391e33fcfd1a5db3bb0a019fa7ce72eac4915906', '7fae0b59e2b3446db84226347d8e119ad1a1c032de1effad1613667869ebbffe'), ('nine-seed38-jones-named-formula-terminal-frontier-independent', '19012c054315ad2215af375ced48d04a83aa2f76bb2a65045fc63d9d4b056751', '213cc37a19e9d221f569a8ba7dbf09bca1ca6c12ca366dc2dbe4ca7af1e9d953')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-named-equality-retry02-draft'
for n,h in [('Norm38MacroNamedVars', 'fba3c1e093ffb3a55e7b6ca5f6bc76f9fd562ff27b3b0c8ba20412bac6de61be'), ('Norm38MacroNamedEquality', 'e04fa148a65dfbe3cce2d641c7afb35fc547902822d829dad2b4d26c6ee2d2c4')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-vars-output-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroVarsOutput', '/tmp/nine-seed38-jones-vars-output-check-20261106/lib/DiophantineConsistency', '068b76a14eb12512b8a83b72feb31be24e2a8a21977bc76998c3b52ff4b1d4b5'), ('Norm38NamedFormula', '/tmp/nine-seed38-jones-named-formula-check-20261106/lib/DiophantineConsistency', 'f628947fecd14dec5840ed18aa4b362c8e1173e6cf4fbdb60722c428e23b2725')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Two audited recipe-output and named-evaluator producers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
