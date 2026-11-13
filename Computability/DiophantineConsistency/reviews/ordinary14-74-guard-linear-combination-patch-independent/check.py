#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-74-guard-linear-combination-patch'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'05c50c1a7ef2b1eeeefe86947c2cea68c083af6634c10c1c28df821e5a191125',A/'OwnZeroGuardStrict74.lean.src':'fa35bca0c3ac35b5876fd48552226ffbc855c7c4d8005e107cb6b8b18d8020d9',A/'check_source.py':'2f81e8a7cd5439eca2ecaf2ab222b0a05a59b12d705db96c9399b8a20a1ffcff',A/'observation.json':'f37bbfa7668e74e207592f3e80903e837863e56ad0a4db1355cbcc2bab97895c'}
tail=b"\nIndependent source review: [74 guard tactic import](../../reviews/ordinary14-74-guard-linear-combination-patch-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='055c32fc130d179330408e80b16ac554eb34ea11d7791d79f3f4788923a30160'
  assert data.endswith(tail) and hashlib.sha256(data[:-len(tail)]).hexdigest()==h
 else:assert H(p)==h,(str(p),H(p),h)
original=D/'research/ordinary14-74-ownzero-guard-strict-draft/OwnZeroGuardStrict74.lean';o=original.read_bytes();b=(A/'OwnZeroGuardStrict74.lean.src').read_bytes()
assert b==b'import Mathlib.Tactic.LinearCombination\n'+o
assert b'linear_combination he' in o and b'import Mathlib.Tactic.LinearCombination' not in o
assert H(original)=='d8d99e58177cdc6fde4fad5f79b577ce97023162656931691ce314141f98e1b8'
source=Path('/home/codex/src/Proofs/.lake/packages/mathlib/Mathlib/Tactic/LinearCombination.lean');assert 'syntax (name := linearCombination) "linear_combination"' in source.read_text()
pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Tactic/LinearCombination.olean');assert pkg.is_file() and H(pkg)=='e4487ef3e033c8a8cfe8562ee7a96d2926444bd73c7f138f265b58a8d1d14c08'
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'exact one-line source delta and bounded tactic/object observation; no Lean, complete import graph or provider coherence','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'original_sha256':H(original),'tactic_source_sha256':H(source),'object_path':str(pkg),'object_realpath':str(pkg.resolve(strict=True)),'object_sha256':H(pkg),'author_receipt_replayed':True},sort_keys=True,indent=2))
