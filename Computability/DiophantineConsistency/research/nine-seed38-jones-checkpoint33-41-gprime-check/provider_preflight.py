#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-checkpoint32-41-f-terminal-frontier-independent', '732935eeaf77d6223734d52755af3f3e99fea7a5d765a6a888404106bcb68b67', 'b66e17e895f38f3a577c40ccbb3bd7a826489107b7e65e89882dde5479d6a4fb'), ('nine-seed38-jones-dependent06-staged-terminal-frontier-independent', 'aee8eeb61486a0934005bf30a063c14d2e297f326192338f5f480b53ffea7044', '78a88923ba6fb795e7638241878dab3603dc19ea664aba10291ae8b115cc6bfd'), ('nine-seed38-jones-checkpoint34-41-terminal-frontier-independent', '0dcf25e14027b11e215e45c105f573e357db9d9e070e9141ea40b5edbdda4282', '840e200729849d89f7be8d82b727dd00dba990998b201885b19ad746ac7e3b7e')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint33-41-gprime-draft'
for n,h in [('Norm38MacroGprimeValue', '08bd07a6fa7a50daf39de9af961b67cdab9b6e83d5d8dc56cfb8605315e9b39c'), ('Norm38MacroGprimePath', 'd9a62e147f8c962f453da82a0e273fd3463d1b65efb20d5d28070a6e1d197df6')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint32-41-f-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroFPath', '/tmp/nine-seed38-jones-checkpoint32-41-f-check-20261106/lib/DiophantineConsistency', '318e2cdfe94a6e1dd389bdb01e3aad9fc32ccac34b1b0bb17e6269bdccb7c11b'), ('Norm38MacroDependentGprime', '/tmp/nine-seed38-jones-dependent06-staged-check-20261106/lib/DiophantineConsistency', 'c2f085832ccfda5cead9ac08d342594c98ee4dcb0d24e2f40def0b92cbd784aa'), ('Norm38MacroCheckpoint34to41', '/tmp/nine-seed38-jones-checkpoint34-41-check-20261106/lib/DiophantineConsistency', '985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Three audited F/Gprime and checkpoint providers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
