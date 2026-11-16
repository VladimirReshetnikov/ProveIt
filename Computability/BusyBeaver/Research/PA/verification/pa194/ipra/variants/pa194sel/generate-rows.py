"""Pin the delivered tables and emit PA194SEL's finite row certificate input."""
import json
import sys
from hashlib import sha256
from pathlib import Path

repo, out = map(Path, sys.argv[1:])
docs = repo / 'Computability/BusyBeaver/Research/PA/docs'
primary = docs / 'pa194_conpa_2026-11-13/construction/tables'
companion = docs / 'pa194_sel_ax11gh_research_2026-11-14/machines/SEL/machine'
pinned = {
    primary / 'pa194.tm': '4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f',
    companion / 'pa194sel.tm': '5121f0b417ea025af140804b59e50a9d2fc3c461612e98b2f0ac86742c76a75b',
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
new = input_table(companion / 'pa194sel.tm')
old_ids = input_labels(primary / 'pa194.labels.json', 'b8c234a0c757cd1885f8fe8ecefc8198767b6d2c15ce0a01443a1e915fded964')
new_ids = input_labels(companion / 'pa194sel.labels.json', 'e9ff4746563f97efc655b1b3b5261d3fb87e5f62aeee3d2fc83cd8be6817d990')
assert set(old_ids) == set(new_ids)
to_new = {x: i for i, x in enumerate(new_ids)}
fold_control = {38:12, 124:127}
rho = [to_new[fold_control.get(x,x)] for x in old_ids]

def render_natives(table, ids):
    rows = {(ids[q], b): (w, d, ids[n]) for (q, b), (w, d, n) in table.items()}
    return ''.join(f"{q} {b} {w} {'R' if d else 'L'} {n}\n"
                   for (q, b), (w, d, n) in sorted(rows.items())).encode()
assert sha256(render_natives(old, old_ids)).hexdigest() == 'e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
assert sha256(render_natives(new, new_ids)).hexdigest() == '98b02254c280a54a763d278841bc33ab8d162f367247c01fa8d2d7cd28acbee1'

def lean_list(seq):
    return '[\n  ' + ',\n  '.join(','.join(map(str,seq[i:i+10])) for i in range(0,len(seq),10))+'\n]'

out.write_text(f"""import PA194BModelSteps

/-! Generated from the pinned primary and PA194SEL literal tables. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194SELRows

abbrev Action := PA194BRows.Action
def primaryLabels : List Nat := {lean_list(old_ids)}
def labels : List Nat := {lean_list(new_ids)}
def targets : List Nat := {lean_list(rho)}
def actions : List Action := {lean_list([str(new[q,b]).replace(' ','') for q in range(194) for b in range(2)])}
def action (q b : Nat) : Action := actions.getD (2*q+b) (0,0,194)
def rho (q : Nat) : Nat := targets.getD q 194

end PA194SELRows
""")
