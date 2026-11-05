#!/usr/bin/env python3
"""Split the captured adapted carrier source without modifying its bodies."""
import hashlib, json, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
P=Path(__file__).resolve().parent
src=D/'research/thirteen-current2011-fresh-model/src/DiophantineConsistency/ModelThirteenCarrier.lean'
raw=src.read_bytes(); h=hashlib.sha256(raw).hexdigest()
if h!='5675f2b35f58069b1b2fbbbc87e00fe2dd808c4e7cf3d364db8dc3c6bede7c10':raise RuntimeError('adapted carrier source drift')
s=raw.decode('utf-8'); prefix_marker='/-! ### Literal thirteen-coordinate syntax -/'
split_marker='/-! ### Completion in every model of `𝗜𝚺₁` -/'
for marker in (prefix_marker,split_marker):
 if s.count(marker)!=1:raise RuntimeError('ambiguous split marker')
head, rest=s.split(prefix_marker); generic, model=rest.split(split_marker)
if not generic.endswith('end Replace\n\n'):raise RuntimeError('unexpected generic boundary')
core=head+prefix_marker+generic+'end DiophantineConsistency.ModelThirteenCarrier\n'
main=head.replace('import FrontierBridge\n','import FrontierBridge\nimport DiophantineConsistency.ModelThirteenCarrierCore\n',1)+split_marker+model
out=P/'src/DiophantineConsistency'
for name,text in [('ModelThirteenCarrierCore.lean',core),('ModelThirteenCarrier.lean',main)]:
 path=out/name
 if path.exists():raise RuntimeError('refuse existing '+str(path))
 path.write_text(text,encoding='utf-8')
print(json.dumps({'adapted_source_sha256':h,'core_sha256':hashlib.sha256(core.encode()).hexdigest(),'remaining_sha256':hashlib.sha256(main.encode()).hexdigest(),'scope':'source-only mechanical split; unchecked Lean'},indent=2,sort_keys=True))
