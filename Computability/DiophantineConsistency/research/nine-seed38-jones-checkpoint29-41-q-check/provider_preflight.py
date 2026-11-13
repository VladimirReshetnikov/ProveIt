#!/usr/bin/env python3
"""Point checks for audited C/Q and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [
 ('nine-seed38-jones-checkpoint26-27-c-terminal-frontier-independent','3fce1d53f4d365c12f042d4d8c6c200f4baa4eb0c9bcf279128bd6c99e0318c8','73cb25f808b7efed49712507b9e25048a5e0295d78373cbc314ffdda4792b31a'),
 ('nine-seed38-jones-dependent04-staged-terminal-frontier-independent','5962b78b76c806f9dc152d2eb8bef8c7faa6699b43293dee30236b1f18d9ed12','3e7d2596e95f280c96ae7e8da8379731390b8db4116fb27fcd3edec9d9db800d'),
 ('nine-seed38-jones-checkpoint34-41-terminal-frontier-independent','0dcf25e14027b11e215e45c105f573e357db9d9e070e9141ea40b5edbdda4282','840e200729849d89f7be8d82b727dd00dba990998b201885b19ad746ac7e3b7e')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint29-41-q-draft'
for n,h in [('Norm38MacroQValue','6d4797045e10282c480515ba44e69fe24614079fa6f56729d4f325f949675978'),('Norm38MacroQPath','2f364886afb7e183db53363eaa8c4065e8661ffd4386b613d3c6051554aaf692')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint26-27-c-check-20261106/lib/DiophantineConsistency')
providers=[
 ('Norm38MacroCValue','/tmp/nine-seed38-jones-checkpoint26-27-c-check-20261106/lib/DiophantineConsistency','460ceb6124d38eedff80b049022612adcd2e4f8a5fbd76dd6e44fcfa532ea764'),
 ('Norm38MacroDependentQ','/tmp/nine-seed38-jones-dependent04-staged-check-20261106/lib/DiophantineConsistency','a306bbaa1f89b688b9a99bcd7146fa0b989eb1c0574810c6197c7a518b461840'),
 ('Norm38MacroCheckpoint34to41','/tmp/nine-seed38-jones-checkpoint34-41-check-20261106/lib/DiophantineConsistency','985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155')]
selected={}
for n,root,h in providers:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Three audited C/Q and checkpoint providers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
