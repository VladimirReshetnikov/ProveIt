#!/usr/bin/env python3
"""Point checks for audited checkpoint and symbolic N providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [
 ('nine-seed38-jones-checkpoint27-34-terminal-frontier-independent','bd31b6a67c1ebf156764984ceefe7553f7783aca0da1c5640af55e009da5d362','ac35881ac2ef66ca8d3c6a26fd127e98a1e8aaee5bb8b2f3246a28f9f3f9631e'),
 ('nine-seed38-jones-live18-staged-terminal-frontier-independent','63ecdb794bbb09df8baa50c7a19c5f1f2de15193c0d3e34ccbc7c1fdd7165765','d4424de55d8afca035515af5bf56899b02ae64e9e7e011fa256021f267d78eac'),
 ('nine-seed38-jones-prefix-group05-terminal-frontier-independent','be57dc896c38e9f6e029d57041979a7edbfdcbed32d857ed97d877018141f423','983d494267643fd48718d104fe302405b7b2d5ea705b00abaf7854594849dbbb')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
if sha(D/'research/nine-seed38-jones-checkpoint34-41-draft/Norm38MacroCheckpoint34to41.lean')!='aadc8c43e1b31996b95a7f9e9d1f7438cd4cd5b845680b38a8b0132e3396572b':raise RuntimeError('source')
base=Path('/tmp/nine-seed38-jones-checkpoint27-34-check-20261106/lib/DiophantineConsistency')
providers=[
 ('Norm38MacroCheckpoint27to34','/tmp/nine-seed38-jones-checkpoint27-34-check-20261106/lib/DiophantineConsistency','92c83d8b5fbd508a804fabfc51aefb184225bda00a0a349d80374677258aab39'),
 ('Norm38MacroLive18Group01','/tmp/nine-seed38-jones-live18-staged-check-20261106/lib/DiophantineConsistency','b2c531a9eecdd13baaf18f2f130949cd8fd7602118f575cd124fffa4b0dc32dd'),
 ('Norm38MacroPrefixQNCarry','/tmp/nine-seed38-jones-prefix-group05-check-20261106/lib/DiophantineConsistency','bd2995f482e56f212b821cb5ced4a9f660119720e20a57cb71aeedf9294c194c')]
selected={}
for n,root,h in providers:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Three audited checkpoint/N providers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
