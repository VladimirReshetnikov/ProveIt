#!/usr/bin/env python3
"""Capture the one direct outside module absent from the BFS outside baseline."""
from hashlib import sha256
from pathlib import Path
import json,os,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1];outside=D/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json'
pin='5ed42b353836c0cae01a838b701347c7a2c9cc84318e893fbe5c4ae0c7c0b777';sha=lambda p:sha256(Path(p).read_bytes()).hexdigest()
assert sha(outside)==pin
n='Mathlib.Algebra.Order.Ring.Basic';assert n not in json.loads(outside.read_text())
pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean');rel=n.replace('.','/');suffixes=('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')
selected=None
for root in (pack,core):
 p=root/(rel+'.olean')
 if os.path.lexists(p):
  assert p.is_file();selected=p;break
assert selected==pack/(rel+'.olean')
records={}
for s in suffixes:
 p=Path(str(selected)[:-6]+s)
 if not os.path.lexists(p):records[s]=None;continue
 assert p.is_file();records[s]={'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
assert records['.olean']['sha256']=='ea83b1b21091681e446b6d29768b758db2523188f511a372f599db4d4f2d9333'
r={'status':'PASS','scope':'one direct outside bundle only; no parent provider or transitive outside closure checked','module':n,'record':records,'outside_baseline_sha256':pin,'capture_sha256':sha(__file__)}
o=H/'observations/outside-attempt01';o.mkdir(parents=True,exist_ok=False);(o/'result.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':'PASS','result_sha256':sha(o/'result.json')}))
