#!/usr/bin/env python3
"""Pin the delivered table bytes and bind both numeric Lean lists to them."""
import hashlib, json, re, sys
from pathlib import Path
root = Path(sys.argv[1])
out = Path(sys.argv[2])
base = root / 'Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/construction/tables'
expected = {
 'pa194.tm':'4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f',
 'pa194_AD.tm':'27613aa92da79ba2ec6e2e88e0ac909fda218e06495ecc0af27201eac0e26c8f',
 'pa194.labels.json':'b8c234a0c757cd1885f8fe8ecefc8198767b6d2c15ce0a01443a1e915fded964',
 'pa194_AD.labels.json':'b8c234a0c757cd1885f8fe8ecefc8198767b6d2c15ce0a01443a1e915fded964',
}
for name, sha in expected.items():
    assert hashlib.sha256((base/name).read_bytes()).hexdigest() == sha, name

def rows(name):
    result=[]
    for i, line in enumerate((base/name).read_text().splitlines()):
        q,b,w,d,n=line.split()
        assert int(q)==i//2 and int(b)==i%2 and w in ('0','1') and d in ('L','R')
        assert 0 <= int(n) <= 194
        result.append((int(w), int(d=='R'), int(n)))
    assert len(result)==388
    return result
p, a = rows('pa194.tm'), rows('pa194_AD.tm')
labels=json.loads((base/'pa194.labels.json').read_text())
assert labels==json.loads((base/'pa194_AD.labels.json').read_text())
assert len(labels)==195 and len(set(labels))==195 and labels[0]==74 and labels[194]==254
assert [(i//2, i%2, p[i], a[i]) for i in range(388) if p[i]!=a[i]] == [
 (109,1,(0,1,95),(0,1,114)), (110,1,(0,1,95),(0,1,114)),
 (124,1,(0,1,114),(0,1,95))]
assert [labels[i] for i in (109,110,124,95,114)]==[161,17,144,32,48]
src=(Path(__file__).parent/'PA194ADTable.lean').read_text()
body=src.split('def adRows : List Action := [',1)[1].split(']',1)[0]
assert [tuple(map(int, x)) for x in re.findall(r'\((\d+),\s*(\d+),\s*(\d+)\)',body)]==a
out.mkdir(parents=True,exist_ok=True)
(out/'PA194Rows.lean').write_text('import Std\nnamespace PA194Rows\ndef rows : List (Nat × Nat × Nat) := [\n'+''.join(f'  ({w}, {d}, {n}),\n' for w,d,n in p[:-1])+f'  ({p[-1][0]}, {p[-1][1]}, {p[-1][2]})\n]\nend PA194Rows\n')
print('Pinned byte hashes, common state labels, and 388 companion rows: verified.')
