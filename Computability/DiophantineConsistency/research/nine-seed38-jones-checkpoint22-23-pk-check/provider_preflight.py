#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-checkpoint35-41-i-terminal-frontier-independent', '5f1492ab0794231b076ee02263581e039e290ad1b138f01dcd5827c4eae1f447', '996c5e322d517f95e6137be4ef126c3ecdae6b7cc1264b375a2eed79393d5813'), ('nine-seed38-jones-dependent02-staged-terminal-frontier-independent', '3fe72c765d785e759248768d743b1f948b2d7ec4146d2d981a938348f06d6bcb', '03f4dd834eb2b106f48865c044c6614712d4f52487540cf6a717f70f8f7375fd'), ('nine-seed38-jones-live18-staged-terminal-frontier-independent', '63ecdb794bbb09df8baa50c7a19c5f1f2de15193c0d3e34ccbc7c1fdd7165765', 'd4424de55d8afca035515af5bf56899b02ae64e9e7e011fa256021f267d78eac'), ('nine-seed38-jones-prefix-group04-staged-terminal-frontier-independent', '31d6811cc6682276bb919729d3bc9f6465802abf6f2a134626cf7bcad193a26e', '153db18a7fbd10ce1ad77c25d25f7eaceeab5f9e2b877821392b4e1416129925')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint22-23-pk-draft'
for n,h in [('Norm38MacroPValue', '3dd46907a518cc86c3c5358c0fbfd39148c77ccbbc18cd3ae37accaa3edd4483'), ('Norm38MacroKValue', 'be84244546ef29c4859396e233f6a86137f7a8f14cf42da6dff6d61fc3deb036')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint35-41-i-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroIPath', '/tmp/nine-seed38-jones-checkpoint35-41-i-check-20261106/lib/DiophantineConsistency', '74e27686b398042b890bbf84d9a2f1638f50b6e57502212fed6c926122212429'), ('Norm38MacroDependentP', '/tmp/nine-seed38-jones-dependent02-staged-check-20261106/lib/DiophantineConsistency', '02d7d218dd922bd33bf7e8f6aad2533855fe157dbd3ea844b5111a335c9db964'), ('Norm38MacroDependentK', '/tmp/nine-seed38-jones-dependent02-staged-check-20261106/lib/DiophantineConsistency', '54542c0eb712eb19b70ae07aef9308156edf7fc4311e177d00fb8181278a5f9d'), ('Norm38MacroLive18Group02', '/tmp/nine-seed38-jones-live18-staged-check-20261106/lib/DiophantineConsistency', 'f028ef640af09a6477b7672e76630057147c859c26d908dafded919953f8a53c'), ('Norm38MacroPrefixInputsA', '/tmp/nine-seed38-jones-prefix-group04-staged-check-20261106/lib/DiophantineConsistency', 'ab8025bff041d6816025d2457dc12f9d5fa4e6072d399a8b8767d16bcbb2faf9')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Four audited I, P/K and input producers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
