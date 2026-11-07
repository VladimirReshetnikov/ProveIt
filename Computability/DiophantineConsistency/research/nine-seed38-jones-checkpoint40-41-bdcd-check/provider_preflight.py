#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-checkpoint38-39-v-terminal-frontier-independent', 'c835f16c721be4835c5b42307af7f8f0b7ba72b3dd7bf0675ce00d412ddba2e2', '643ce4024efb7c650b1752be09019c13a4be171c944f9aa14f3d1ab21217c274'), ('nine-seed38-jones-checkpoint27-34-terminal-frontier-independent', 'bd31b6a67c1ebf156764984ceefe7553f7783aca0da1c5640af55e009da5d362', 'ac35881ac2ef66ca8d3c6a26fd127e98a1e8aaee5bb8b2f3246a28f9f3f9631e'), ('nine-seed38-jones-checkpoint34-41-terminal-frontier-independent', '0dcf25e14027b11e215e45c105f573e357db9d9e070e9141ea40b5edbdda4282', '840e200729849d89f7be8d82b727dd00dba990998b201885b19ad746ac7e3b7e'), ('nine-seed38-jones-dependent08-staged-terminal-frontier-independent', 'c9093ca2c52b810bf0f2d878bb513aa54502b0b2fa13146b11e4e35fbf62d26e', 'f59e7238d645a2eebab7b13fd342d5a1045ea3b53331e7e40620b2223407678c')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint40-41-bdcd-draft'
for n,h in [('Norm38MacroBdCdPaths', 'c6a94c2fd8de8ba867e19584545f81c603e18f0a85e838a8f1be5b19e7784a4e'), ('Norm38MacroBdValue', '5e940e74c66e180d39493ea872279676628087f802cb4f792a0f7e7c56d18a4d'), ('Norm38MacroCdValue', 'b715d04d238e6b4ab467764120749e64b06fa8c93baedad9c9541e2c56519b36')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint38-39-v-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroV1Value', '/tmp/nine-seed38-jones-checkpoint38-39-v-check-20261106/lib/DiophantineConsistency', '018456792e32aa046e8606769b7f8bbde3e53e8e1cf8c004f740ba7ebbb51601'), ('Norm38MacroCheckpoint27to34', '/tmp/nine-seed38-jones-checkpoint27-34-check-20261106/lib/DiophantineConsistency', '92c83d8b5fbd508a804fabfc51aefb184225bda00a0a349d80374677258aab39'), ('Norm38MacroCheckpoint34to41', '/tmp/nine-seed38-jones-checkpoint34-41-check-20261106/lib/DiophantineConsistency', '985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155'), ('Norm38MacroDependentBdCd', '/tmp/nine-seed38-jones-dependent08-staged-check-20261106/lib/DiophantineConsistency', 'c9f93896685c99df7b3dfdaf783d427f6a1150aeb48f70d56a9435597ce22940')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Four audited V, checkpoint and Bd/Cd-node producers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
