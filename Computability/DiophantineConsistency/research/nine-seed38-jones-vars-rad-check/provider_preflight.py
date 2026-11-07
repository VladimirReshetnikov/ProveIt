#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-vars-cd-terminal-frontier-independent', 'b6d778507b1b8c0d695c613b6fba0a05f87df988657ebc49a3dab7f599b67de0', 'd3b890354adbfacc04b97abfbfd72b87de06bb200ada14a52e4957840885d499')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-vars-rad-draft'
for n,h in [('Norm38MacroVarsRad0', '15b8415073861f7ff7f32a25804fcc3c8c22163aa710bccc633d04dfaf7036c7'), ('Norm38MacroVarsRad1', '402cdf6d0bde2f0f0cbb14e28942a92f2ed50aa48b03c7465a1d54de8d221c5a')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-vars-cd-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroVarsCd', '/tmp/nine-seed38-jones-vars-cd-check-20261106/lib/DiophantineConsistency', '1dfc9cbdefc4f7ec437dd2acd3b09bd1668897e263bdfa96c8ffe5182e349138')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'One audited RingVars/Cd producer; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
