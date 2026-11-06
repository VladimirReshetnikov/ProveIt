#!/usr/bin/env python3
"""Point checks for audited checkpoint and symbolic g/G providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [
 ('nine-seed38-jones-checkpoint34-41-terminal-frontier-independent','0dcf25e14027b11e215e45c105f573e357db9d9e070e9141ea40b5edbdda4282','840e200729849d89f7be8d82b727dd00dba990998b201885b19ad746ac7e3b7e'),
 ('nine-seed38-jones-live18-staged-terminal-frontier-independent','63ecdb794bbb09df8baa50c7a19c5f1f2de15193c0d3e34ccbc7c1fdd7165765','d4424de55d8afca035515af5bf56899b02ae64e9e7e011fa256021f267d78eac'),
 ('nine-seed38-jones-prefix-group03-staged-terminal-frontier-independent','7ff8505e755090bf5b29abe4b074bcd36546ed597cc43405b9e4ea6a87c72745','2742892c8e514ac28db872993d219c639faf84961fd18f4852a03e01de81c8e3')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
if sha(D/'research/nine-seed38-jones-checkpoint41-45-draft/Norm38MacroCheckpoint41to45.lean')!='606c7c153863e98662eadb430b442cc28bebec34e4676446b2066c5b6eedf249':raise RuntimeError('source')
base=Path('/tmp/nine-seed38-jones-checkpoint34-41-check-20261106/lib/DiophantineConsistency')
providers=[
 ('Norm38MacroCheckpoint34to41','/tmp/nine-seed38-jones-checkpoint34-41-check-20261106/lib/DiophantineConsistency','985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155'),
 ('Norm38MacroLive18Group01','/tmp/nine-seed38-jones-live18-staged-check-20261106/lib/DiophantineConsistency','b2c531a9eecdd13baaf18f2f130949cd8fd7602118f575cd124fffa4b0dc32dd'),
 ('Norm38MacroLive18Group02','/tmp/nine-seed38-jones-live18-staged-check-20261106/lib/DiophantineConsistency','f028ef640af09a6477b7672e76630057147c859c26d908dafded919953f8a53c'),
 ('Norm38MacroPrefixGsmall','/tmp/nine-seed38-jones-prefix-group03-staged-check-20261106/lib/DiophantineConsistency','dd500df7b9ea630528181ee3e1ac62f955822471a9f3385e0a833c13758dbaf2'),
 ('Norm38MacroPrefixGlarge','/tmp/nine-seed38-jones-prefix-group03-staged-check-20261106/lib/DiophantineConsistency','b685399878adfa8efc0fae22b6f9793c1f74079b4266cfff15d86a6a25e89a06')]
selected={}
for n,root,h in providers:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Five audited checkpoint/g/G providers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
