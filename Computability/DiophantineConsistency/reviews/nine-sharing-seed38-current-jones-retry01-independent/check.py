#!/usr/bin/env python3
"""Verify the exact retry delta; no Lean invocation."""
import hashlib,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];a=D/'research/nine-sharing-seed38-current-jones-client';b=D/'research/nine-sharing-seed38-current-jones-retry01';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(b/'run.py')=='e3e308a08d6f8573cfaf4084515cbe1d9312e2e2424cb123d2886ddaade241fb' and sha(b/'source-manifest.json')=='5681ced6cac0c695af73497609b13df4415ee880fc7b23209f2224c3f33e45bc'
old=(a/'src/DiophantineConsistency/SharingSeed38CurrentJones.lean').read_text();newpath=b/'src/DiophantineConsistency/SharingSeed38CurrentJones.lean';new=newpath.read_text();assert sha(newpath)=='f79ed57d31a864dd389b136ca750a372e1435fad19e190652358df6b4490b61e'
before='one_lt_pow₀ (by decide : 1 < CurrentMasks2011.radix) (by decide)';after='one_lt_pow₀ (by unfold CurrentMasks2011.radix; decide : 1 < CurrentMasks2011.radix) (by decide)';assert old.count(before)==1 and old.replace(before,after)==new
old=(a/'run.py').read_text();new=(b/'run.py').read_text();assert old.replace('nine-sharing-seed38-current-jones-20261105','nine-sharing-seed38-current-jones-retry01-20261105').replace('9a8e3a85c20440199f28c1f857dfd885cffdee87b2028e41c763fdc947a79b78','5681ced6cac0c695af73497609b13df4415ee880fc7b23209f2224c3f33e45bc')==new
print('PASS_EXACT_RETRY_DELTA_ONLY: one radix-unfold proof change; output path and manifest pin only in runner; no Lean run')
