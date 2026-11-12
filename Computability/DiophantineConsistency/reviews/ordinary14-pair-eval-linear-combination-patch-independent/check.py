#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=D.parents[1];A=D/'research/ordinary14-pair-eval-linear-combination-patch';SRC=D/'research/ordinary14-pair-eval-ring-bridge-draft/PairEvalRingBridge.lean';OBJ=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Tactic/LinearCombination.olean');TACTIC=Path('/home/codex/src/Proofs/.lake/packages/mathlib/Mathlib/Tactic/LinearCombination.lean')
def H(data):return hashlib.sha256(data).hexdigest()
pins={A/'README.md':'5ac289b73e59250d8c6f5a95a9bfa6a0cb78e765390e4f459513ef6d54c4febb',A/'PairEvalRingBridge.lean.src':'d0fbb03d62ed66af06944cedd9839e213a411a1e5b9cc85bfb3716b4ac95d3bf',A/'check_source.py':'cd694be7146f9cb83d0fd133b4834b3dbf15351765fff13c9c2b8c231b11d7ed',A/'observation.json':'0b672596ca35722b76d811268682358ad5ad47b1e0fd1655813d3673e3ffbc61',SRC:'0fdb641db2008362ae3ec363bea66f6b4a4b475c1de2d5d00b7c1e9a81adc510',TACTIC:'a59009a15dc914d2774e01cfb1afcbf6490e9e1015587f2ab89c22a2778f2e6d'}
tail=b"\nIndependent source review: [explicit tactic import](../../reviews/ordinary14-pair-eval-linear-combination-patch-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert H(data)=='7fc12c6666a6dca50d0d9ee4b6fba84d2b43efaf9a66d50a5733ac93d0fe1386'
  assert data.endswith(tail) and H(data[:-len(tail)])==h
 else:assert H(p.read_bytes())==h,(str(p),H(p.read_bytes()),h)
orig=SRC.read_bytes();patched=(A/'PairEvalRingBridge.lean.src').read_bytes();assert patched==b'import Mathlib.Tactic.LinearCombination\n'+orig
assert b'linear_combination hs + h' in orig and b'syntax (name := linearCombination) "linear_combination"' in TACTIC.read_bytes()
ref='ada78abffd5784cb6beaec297cf42f10d29494b1:Computability/DiophantineConsistency/research/ordinary14-pair-eval-ring-bridge-draft/PairEvalRingBridge.lean'
committed=subprocess.run(['git','show',ref],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True).stdout
assert committed==orig
assert str(OBJ.resolve(strict=True))=='/home/codex/src/Proofs/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/LinearCombination.olean'
assert H(OBJ.read_bytes())=='e4487ef3e033c8a8cfe8562ee7a96d2926444bd73c7f138f265b58a8d1d14c08'
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=30);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'one-line byte delta, committed baseline, tactic source/object and author receipt only; no Lean or provider closure','pins':{str(p):h for p,h in pins.items()},'committed_baseline':ref,'object_realpath':str(OBJ.resolve(strict=True)),'object_sha256':H(OBJ.read_bytes()),'exact_prefix_only':True,'author_receipt_replayed':True},sort_keys=True,indent=2))
