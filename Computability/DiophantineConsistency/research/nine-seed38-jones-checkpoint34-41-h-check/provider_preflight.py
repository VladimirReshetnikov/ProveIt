#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-checkpoint33-41-gprime-terminal-frontier-independent', 'c8f34bdd959f82ed77df8d665efb843f6de2dfdec274620cd770e57893c6c2bc', '8a5566c1cdb9e0f00ad5490759a17e2df39bdeea5d0a27deac2a453a457a2d5a'), ('nine-seed38-jones-dependent06-staged-terminal-frontier-independent', 'aee8eeb61486a0934005bf30a063c14d2e297f326192338f5f480b53ffea7044', '78a88923ba6fb795e7638241878dab3603dc19ea664aba10291ae8b115cc6bfd'), ('nine-seed38-jones-live18-staged-terminal-frontier-independent', '63ecdb794bbb09df8baa50c7a19c5f1f2de15193c0d3e34ccbc7c1fdd7165765', 'd4424de55d8afca035515af5bf56899b02ae64e9e7e011fa256021f267d78eac'), ('nine-seed38-jones-prefix-group04-staged-terminal-frontier-independent', '31d6811cc6682276bb919729d3bc9f6465802abf6f2a134626cf7bcad193a26e', '153db18a7fbd10ce1ad77c25d25f7eaceeab5f9e2b877821392b4e1416129925'), ('nine-seed38-jones-checkpoint34-41-terminal-frontier-independent', '0dcf25e14027b11e215e45c105f573e357db9d9e070e9141ea40b5edbdda4282', '840e200729849d89f7be8d82b727dd00dba990998b201885b19ad746ac7e3b7e')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint34-41-h-draft'
for n,h in [('Norm38MacroHValue', '38c4fe586e7402168a26593eac5748b07f01a2b2053bc7587c61a52698f9e04e'), ('Norm38MacroHPath', 'b149c812956a3bcd8cfd4cae5bd87ab7d1c2e8936dd0fc1d53477d2cdf2fa49c')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint33-41-gprime-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroGprimePath', '/tmp/nine-seed38-jones-checkpoint33-41-gprime-check-20261106/lib/DiophantineConsistency', '1acfb8bf9673da2c44296cf28e642112c6018d1c25f434a420951b33352287da'), ('Norm38MacroDependentH', '/tmp/nine-seed38-jones-dependent06-staged-check-20261106/lib/DiophantineConsistency', 'fd1691414fc25dab60414cdb181d1c92bcacffc621ee3fb19a6804008d4850ce'), ('Norm38MacroLive18Group04', '/tmp/nine-seed38-jones-live18-staged-check-20261106/lib/DiophantineConsistency', 'd441a380efaacb979a20ed3370cfec35c900afd19d23eaa210b1b7d6bb76c143'), ('Norm38MacroPrefixInputsB', '/tmp/nine-seed38-jones-prefix-group04-staged-check-20261106/lib/DiophantineConsistency', '43b71a21b7efa4d263709791c323ac49005a3e3b28542836890e094710474170'), ('Norm38MacroCheckpoint34to41', '/tmp/nine-seed38-jones-checkpoint34-41-check-20261106/lib/DiophantineConsistency', '985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Five audited Gprime/H and inputs and checkpoint providers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
