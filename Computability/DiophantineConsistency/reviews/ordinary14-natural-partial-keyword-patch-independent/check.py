#!/usr/bin/env python3
"""Review pinned parser evidence and inert source renames; never invoke Lean."""
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2]; P=D/'research/ordinary14-natural-partial-keyword-patch'; O=D/'research/ordinary14-natural81-combined-slim-overlay/source'
L=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Lean/Parser')
def pin(path,h):
 b=path.read_bytes(); assert hashlib.sha256(b).hexdigest()==h,str(path); return b.decode()
command=pin(L/'Command.lean','e4afed93ed1a2de7d56df108f9d5963f0495489936f4bc4b48d6c9742c90ed03')
basic=pin(L/'Basic.lean','52bc0d189a600e760fde91f55e1429d9a612b1a63452da063ee74de9ed3f3d8e')
assert 'def «partial»        := leading_parser "partial "' in command
assert 'optional («partial» <|> «nonrec»)' in command
assert 'def declId := leading_parser\n  ident >>' in command
assert 'if a token is both a symbol and a valid identifier (i.e. a keyword)' in basic
assert 'if isToken startPos stopPos tk then' in basic
assert len(list(O.glob('*.lean.src')))==173
pattern=re.compile(r"(?<![A-Za-z0-9_'])partial(?![A-Za-z0-9_'])")
files=[x.name for x in O.glob('*.lean.src') if pattern.search(x.read_text())]
assert set(files)=={'PartialShift82To74.lean.src','GraphPredecessors82.lean.src'}
counts={}
for name,digest,n in [('PartialShift82To74','47cb83c7a8cf4053e19eb7afbb391e00528b8b0ce5fdf4a2edda9c909163170e',8),('GraphPredecessors82','44c47be7c5725bd5bbe11ed810780938c3b885eb394ae69d5bfc9797d8ce9c5e',7)]:
 original=(O/(name+'.lean.src')).read_text(); patch=pin(P/(name+'.lean.src'),digest)
 out=[]; count=0
 for line in original.splitlines(keepends=True):
  if line.lstrip().startswith('/--'): out.append(line); continue
  line,k=pattern.subn('partialValuation',line); count+=k; out.append(line)
 assert count==n and ''.join(out)==patch
 assert not any(pattern.search(line) for line in patch.splitlines() if not line.lstrip().startswith('/--'))
 counts[name]=count
print(json.dumps({'scope':'pinned parser-source and inert textual comparison; no Lean parsing or theorem','overlay_modules_scanned':173,'source_files_with_token':sorted(files),'renames':counts},sort_keys=True,indent=2))
