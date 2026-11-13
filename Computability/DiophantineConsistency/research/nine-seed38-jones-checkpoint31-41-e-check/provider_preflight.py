#!/usr/bin/env python3
"""Point checks for audited D/E, input, J and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-checkpoint30-41-d-terminal-frontier-independent', 'cc91a60cdcc9f2f25ebdfd46e7b4d599eadb94168b697c1fe4e050f01bc95feb', '8da65ad04ba60ef297222592143f8ba2e709ed1b85e15a338b19962b1d5430f3'), ('nine-seed38-jones-dependent05-staged-terminal-frontier-independent', '4a0b38cafb87dfdbaf3e0aa4c8038f1d0f595992903814632316b4dd80988bed', '032d6f20599ed912ba688e6fbe24697fd7ec8a5742df1b9de9442f2f653b1f44'), ('nine-seed38-jones-live18-staged-terminal-frontier-independent', '63ecdb794bbb09df8baa50c7a19c5f1f2de15193c0d3e34ccbc7c1fdd7165765', 'd4424de55d8afca035515af5bf56899b02ae64e9e7e011fa256021f267d78eac'), ('nine-seed38-jones-prefix-group04-staged-terminal-frontier-independent', '31d6811cc6682276bb919729d3bc9f6465802abf6f2a134626cf7bcad193a26e', '153db18a7fbd10ce1ad77c25d25f7eaceeab5f9e2b877821392b4e1416129925'), ('nine-seed38-jones-checkpoint28-41-j-terminal-frontier-independent', '9b3d130b31010f0014a7de606b93fb2e3ede9894d1c5b39481677b836909beb9', '6f82d237aee6711a54c0c48dcd3e94a8148ff8d614d0821b18215f792e4a1f7a'), ('nine-seed38-jones-checkpoint34-41-terminal-frontier-independent', '0dcf25e14027b11e215e45c105f573e357db9d9e070e9141ea40b5edbdda4282', '840e200729849d89f7be8d82b727dd00dba990998b201885b19ad746ac7e3b7e')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint31-41-e-draft'
for n,h in [('Norm38MacroEValue', 'd2510ec44441cdcd46e231343944659c876312a5798dc692b7fbfa368107e16f'), ('Norm38MacroEPath', 'c9e0519b4dee63ac8ec19ca7c113ae747e3da4a916dddf2bfedeef7830541dd8')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint30-41-d-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroDPath', '/tmp/nine-seed38-jones-checkpoint30-41-d-check-20261106/lib/DiophantineConsistency', '3eeb262b43d939b4af764a026281d006c0d7c05fecda77dba04fa28a9ced85db'), ('Norm38MacroDependentE', '/tmp/nine-seed38-jones-dependent05-staged-check-20261106/lib/DiophantineConsistency', 'bc5eda5787bcabd4e9ae026819ab20bb299dfdd4aff76d59f7e3e3dc9fb85433'), ('Norm38MacroLive18Group04', '/tmp/nine-seed38-jones-live18-staged-check-20261106/lib/DiophantineConsistency', 'd441a380efaacb979a20ed3370cfec35c900afd19d23eaa210b1b7d6bb76c143'), ('Norm38MacroPrefixInputsB', '/tmp/nine-seed38-jones-prefix-group04-staged-check-20261106/lib/DiophantineConsistency', '43b71a21b7efa4d263709791c323ac49005a3e3b28542836890e094710474170'), ('Norm38MacroJValue', '/tmp/nine-seed38-jones-checkpoint28-41-j-check-20261106/lib/DiophantineConsistency', 'c6e4b69ed5e03ed41171bb6b85dada829f43625dc901b7de14f18305d8ac87a4'), ('Norm38MacroCheckpoint34to41', '/tmp/nine-seed38-jones-checkpoint34-41-check-20261106/lib/DiophantineConsistency', '985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Six audited D/E, input, J and checkpoint providers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
