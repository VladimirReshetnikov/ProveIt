#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-vars-rad-terminal-frontier-independent', 'a49deb85df7cd0810489c5fa0f9b2412add46ef498becacc754d1557e82af276', '465b52e44e9038124010290b69104f64b08506a67ff03f3f4119d441b98c1d0a')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-vars-wt-draft'
for n,h in [('Norm38MacroVarsWt0', '8798255354b32257ba2f0daaeee61e71d7fc32ea79238a0b5d7347fadab50f45'), ('Norm38MacroVarsWt1', '4c438960a38a6e12ce16cc3d0d20e4d4e16f16da68fa8ae45b7c591be780a056')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-vars-rad-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroVarsRad1', '/tmp/nine-seed38-jones-vars-rad-check-20261106/lib/DiophantineConsistency', '76684ed48a14cc0329ccd3000599e76b1dfcc420aae03bfb8a6ff3b711850fc2')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'One audited RingVars radicand producer; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
