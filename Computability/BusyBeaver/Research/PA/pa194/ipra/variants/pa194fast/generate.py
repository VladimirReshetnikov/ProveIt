"""Generate Lean rows for the bytes of the delivered native primary_fast table."""
import json
from hashlib import sha256
from pathlib import Path
import sys

repo, out = map(Path, sys.argv[1:])
docs = repo / 'Computability/BusyBeaver/Research/PA/docs'
primary = docs / 'pa194_conpa_2026-11-13/construction/tables'
pins = docs / 'pa194_ax11gdh_research_2026-11-15/research/core_reductions/input_sha256.json'
record = json.loads(pins.read_bytes())
labels_bytes = (primary / 'pa194.labels.json').read_bytes()
primary_bytes = (primary / 'pa194.tm').read_bytes()
assert sha256(labels_bytes).hexdigest() == record['inputs/labels.json']
assert sha256(primary_bytes).hexdigest() == record['inputs/primary.tm']
labels = json.loads(labels_bytes)
dense = {q: i for i, q in enumerate(labels)}
assert len(labels) == len(dense) == 195 and (labels[0], labels[-1]) == (74, 254)
native = {}
for line in primary_bytes.decode('ascii').splitlines():
    q, b, w, move, dest = line.split()
    native[labels[int(q)], int(b)] = int(w), move, labels[int(dest)]
assert set(native) == {(q, b) for q in labels[:-1] for b in (0, 1)}
native[26, 1] = 1, 'R', 91
native[101, 0] = 0, 'R', 17
literal = ''.join(f'{q} {b} {w} {m} {r}\n' for (q,b), (w,m,r) in sorted(native.items())).encode('ascii')
assert sha256(literal).hexdigest() == record['inputs/primary_fast.native.tm']
out.mkdir(parents=True, exist_ok=True)
(out / 'primary_fast.native.tm').write_bytes(literal)
rows = []
for q in labels[:-1]:
    for b in (0, 1):
        w, m, r = native[q, b]
        rows.append(f'({w},{int(m == "R")},{dense[r]})')
chunks = ',\n'.join('  '+','.join(rows[i:i+12]) for i in range(0, len(rows), 12))
post = """
]
def action (q b : Nat) : Action := rows.getD (2*q+b) (0,0,194)
def oldAction (q b : Nat) : Action := PA194Rows.rows.getD (2*q+b) (0,0,194)
abbrev table := PA194BModelSteps.table rows
abbrev oldTable := PA194BModelSteps.table PA194Rows.rows
theorem rowCount : rows.length = 388 := by decide +kernel

theorem sameExcept : ∀ q : Fin 194, ∀ b : Fin 2,
    (q.val ≠ 65 ∨ b.val ≠ 1) → (q.val ≠ 111 ∨ b.val ≠ 0) →
      action q.val b.val = oldAction q.val b.val := by
  decide +kernel

theorem incoming : ∀ q : Fin 194, ∀ b : Fin 2,
    let a := action q.val b.val
    a.2.2 < 195 ∧
    (a.2.2 = 111 → a.1 = 0 ∧ a.2.1 = 1) ∧
    (a.2.2 = 46 → a.1 = 0) ∧
    (a.2.2 = 65 → q.val = 46 ∧ b.val = 0 ∧ a.1 = 0 ∧ a.2.1 = 0) := by
  decide +kernel

#print axioms sameExcept
#print axioms incoming
end PA194FastRows
"""
(out / 'PA194FastRows.lean').write_text("""import PA194BModelSteps

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194FastRows
open PA194BRows (Action)

/-- Dense rows obtained from the pinned native primary_fast bytes using the
    primary native-to-dense map. -/
def rows : List Action := [
""" + chunks + post)
