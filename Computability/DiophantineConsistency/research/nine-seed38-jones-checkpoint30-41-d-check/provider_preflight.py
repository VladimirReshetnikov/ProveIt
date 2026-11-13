#!/usr/bin/env python3
"""Point checks for audited Q/A/D and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [
 ('nine-seed38-jones-checkpoint24-27-a-terminal-frontier-independent','ef19ae5429be1e3111854ff8d3c946d926da40229c24c9efc1f72b84412c23a3','b9bf76ff10dc86087eacfc95e05417276c485f9722f4391c22bcf9836f3101f4'),
 ('nine-seed38-jones-checkpoint29-41-q-terminal-frontier-independent','33db0939c1ec98ec80f43ac06c7c178b20712f3a2068c030cd548c4915b1176d','9e176d06fa0ae167efa07eaaf4a5403896b866ffdfdda430b6f1a1dfe0ebe846'),
 ('nine-seed38-jones-dependent04-staged-terminal-frontier-independent','5962b78b76c806f9dc152d2eb8bef8c7faa6699b43293dee30236b1f18d9ed12','3e7d2596e95f280c96ae7e8da8379731390b8db4116fb27fcd3edec9d9db800d'),
 ('nine-seed38-jones-checkpoint34-41-terminal-frontier-independent','0dcf25e14027b11e215e45c105f573e357db9d9e070e9141ea40b5edbdda4282','840e200729849d89f7be8d82b727dd00dba990998b201885b19ad746ac7e3b7e')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint30-41-d-draft'
for n,h in [('Norm38MacroDValue','89f84475000478fd9112a8f76a599b5f5aa49413a765a23c797c70ecf180ee45'),('Norm38MacroDPath','d8118d169de7ff5769816971817b78787bb3f1335bba2ac86709f3073279b53e')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint29-41-q-check-20261106/lib/DiophantineConsistency')
providers=[
 ('Norm38MacroAValue','/tmp/nine-seed38-jones-checkpoint24-27-a-check-20261106/lib/DiophantineConsistency','e22058fcc79740fc425fbb063007e3022a6cdc75b217385fb961a3e173dc0a31'),
 ('Norm38MacroQPath','/tmp/nine-seed38-jones-checkpoint29-41-q-check-20261106/lib/DiophantineConsistency','9b68e1bba3d3d8379632864ee79f363733d4a705b6846c08809b4e0581be55c8'),
 ('Norm38MacroDependentD','/tmp/nine-seed38-jones-dependent04-staged-check-20261106/lib/DiophantineConsistency','3fb3464ef223d9d0e7dc33fccd7d1845337aea9ccc9184c137e6664bc2026931'),
 ('Norm38MacroCheckpoint34to41','/tmp/nine-seed38-jones-checkpoint34-41-check-20261106/lib/DiophantineConsistency','985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155')]
selected={}
for n,root,h in providers:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Four audited Q/A/D and checkpoint providers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
