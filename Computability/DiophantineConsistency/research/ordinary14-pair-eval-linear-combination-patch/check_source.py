#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
orig=D/'research/ordinary14-pair-eval-ring-bridge-draft/PairEvalRingBridge.lean';patched=P/'PairEvalRingBridge.lean.src';prefix=b'import Mathlib.Tactic.LinearCombination\n'
a=orig.read_bytes();b=patched.read_bytes();assert b==prefix+a and prefix not in a and b'linear_combination hs + h' in a
pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Tactic/LinearCombination.olean')
def H(x):return hashlib.sha256(x.read_bytes()).hexdigest()
assert pkg.is_file()
print(json.dumps({'scope':'exact source delta and selected object observation only; no Lean, dependency closure or provider proof','original_sha256':H(orig),'patched_sha256':H(patched),'added_line':prefix.decode().strip(),'package_object':str(pkg),'object_realpath':str(pkg.resolve(strict=True)),'object_sha256':H(pkg)},sort_keys=True,indent=2))
