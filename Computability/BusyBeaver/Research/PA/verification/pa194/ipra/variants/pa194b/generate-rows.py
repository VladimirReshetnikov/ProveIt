"""Pin the delivered tables and emit PA194B's finite row certificate input."""
import json
import sys
from hashlib import sha256
from pathlib import Path

repo, out = map(Path, sys.argv[1:])
docs = repo / 'Computability/BusyBeaver/Research/PA/docs'
primary = docs / 'pa194_conpa_2026-11-13/construction/tables'
companion = docs / 'PA194B_PA194G_research_2026-11-14/machine'
pinned = {
    primary / 'pa194.tm': '4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f',
    companion / 'pa194B.tm': 'b2bcdb6c3816a1fbade699a79e431e4b530ec341aaf516c911920d43f9995397',
}

def input_table(path):
    buf = path.read_bytes()
    assert sha256(buf).hexdigest() == pinned[path]
    entries = {}
    for line in buf.decode('ascii').splitlines():
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, [q, b, w, n])
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R') and 0 <= n <= 194
        assert (q, b) not in entries
        entries[q, b] = (w, int(d == 'R'), n)
    assert set(entries) == {(q,b) for q in range(194) for b in range(2)}
    return entries

def input_labels(path, expected):
    contents = path.read_bytes()
    assert sha256(contents).hexdigest() == expected
    data = json.loads(contents)
    assert len(data) == len(set(data)) == 195
    assert data[0] == 74 and data[-1] == 254
    return data

old = input_table(primary / 'pa194.tm')
new = input_table(companion / 'pa194B.tm')
old_ids = input_labels(primary / 'pa194.labels.json', 'b8c234a0c757cd1885f8fe8ecefc8198767b6d2c15ce0a01443a1e915fded964')
new_ids = input_labels(companion / 'pa194B.labels.json', 'e30b9614e7d105cdb50d1c9fdb82c4051b58e4d46b7bb7602714094f4e3c64b5')
assert set(old_ids) == set(new_ids)
to_new = {x: i for i, x in enumerate(new_ids)}
rho = [to_new[88 if x == 301 else x] for x in old_ids]

def render_natives(table, ids):
    rows = {(ids[q], b): (w, d, ids[n]) for (q, b), (w, d, n) in table.items()}
    return ''.join(f"{q} {b} {w} {'R' if d else 'L'} {n}\n"
                   for (q, b), (w, d, n) in sorted(rows.items())).encode()
assert sha256(render_natives(old, old_ids)).hexdigest() == 'e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
assert sha256(render_natives(new, new_ids)).hexdigest() == 'f9d8b134f99b669d2339b92e062100d5ad854874a23bd8f8aa1141821667d08e'

def lean_list(seq):
    return '[\n  ' + ',\n  '.join(','.join(map(str,seq[i:i+10])) for i in range(0,len(seq),10))+'\n]'

out.write_text(f"""import PA194GenericBridge

/-! Generated from the pinned primary and PA194B literal tables. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194BRows

abbrev Action := Nat × Nat × Nat
def primaryLabels : List Nat := {lean_list(old_ids)}
def labels : List Nat := {lean_list(new_ids)}
def targets : List Nat := {lean_list(rho)}
def actions : List Action := {lean_list([str(new[q,b]).replace(' ','') for q in range(194) for b in range(2)])}
def action (q b : Nat) : Action := actions.getD (2*q+b) (0,0,194)
def primary (q b : Nat) : Action := PA194Rows.rows.getD (2*q+b) (0,0,194)
def rho (q : Nat) : Nat := targets.getD q 194

end PA194BRows
""")
