"""Build dag222: K230's Dag230 with the AX node 236 rebuilt for the seed-K 222 (variant-bc /
Source 131): the rho7 row word (ax[19:30]) becomes Source 128's G word, and the bundle span
(the contract's original word at 88) becomes the helper-free seed bundle word. All other nodes
keep their numbers. Writes dag222_nodes.json, dag222_sites.json and the new word.
The new bundle word is checked against the pinned symbolic executor first."""
import json, sys, os, importlib.util, hashlib
sys.path.insert(0, os.path.dirname(__file__))
from dagmodel import parse, atoms_of, expand, sites
from pathlib import Path

S = Path(r"C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-merge-article-groups-491e11\31b37d1b-6b02-4181-babf-8c85ac50cb17\scratchpad")
V = S / "rocq225/pkg/vendor/k230-rocq/coq/prog"
K224 = S / "intake181/fresh/K224_Construction_2026-10-20/K224_Construction_2026-10-20/portable"
C = json.load(open(K224 / "theory/emitter_contract.json"))
G129 = json.load(open(S / "intake186/fresh/c/K223_Construction_2026-10-20/portable/machine/grammar223.json"))
em = K224 / "verification/check_emitter.py"
assert hashlib.sha256(em.read_bytes()).hexdigest().startswith("32fa8462")
spec = importlib.util.spec_from_file_location("e", em); ex = importlib.util.module_from_spec(spec); spec.loader.exec_module(ex)

nodes = parse(V / "Dag230.v")
atoms = atoms_of(V / "ProgLib230.v")
word = expand(nodes, ("N", 236), atoms)
ids = [e[1] if e[0] == "N" else None for e in word]
old_r7 = [168, 166, 182, 168, 121, 182, 166, 121, 182, 119, 119]
new_g = [168, 166, 182, 168, 121, 182, 166, 121, 181, 166, 121, 182, 180, 119, 119]
assert ids[19:30] == old_r7
assert ids[88:88 + len(C["original_word"])] == C["original_word"]
w129 = G129["macro_word"]
rv_word = [166, 121, 181, 168, 166, 121, 181, 180, 119]
h_word = [166, 121, 182, 166, 121, 181, 166, 121, 182, 180, 119]
assert w129[:9] == rv_word and w129[9:20] == h_word and w129[-3:] == [119, 119, 218]
bundle222 = rv_word + w129[20:-3] + [119, 218]
I, R, Q, E, N = ex.I, ex.R, ex.Q, ex.E, ex.N
rv = I(R("a", "b"), Q("c", R("a", "b")))
core = ex.execute(w129[20:-3])
assert ex.execute(bundle222) == N(I(rv, core))
assert ex.execute(new_g) == I(E("c", "a"), I(E("c", "b"), Q(R("a", "b"), E("a", "b"))))
lo, hi = 88, 88 + len(C["original_word"])
new_ids = ids[:19] + new_g + ids[30:lo] + bundle222 + ids[hi:]
new_word = [("N", x) for x in new_ids]
assert all(e[1] in atoms for e in new_word)

N2 = dict(nodes)
chain = [236] + list(range(301, 301 + len(new_word) - 2))
for i, n in enumerate(chain):
    a = new_word[i]
    b = ("N", chain[i + 1]) if i + 1 < len(chain) else new_word[i + 1]
    N2[n] = (a, b)
nn = max(N2) + 1
assert expand(N2, ("N", 236), atoms) == new_word
out = S / "k224rocq"
json.dump({"nnodes": nn, "nodes": {str(k): [list(v[0]), list(v[1])] for k, v in sorted(N2.items())},
           "word236": new_ids, "bundle222": bundle222, "g_row": new_g, "core_expression": core},
          open(out / "dag222_nodes.json", "w"))
json.dump(sites(N2, 0, nn), open(out / "dag222_sites.json", "w"))
print("dag222: nnodes", nn, "AX word", len(ids), "->", len(new_ids), "| bundle word", len(bundle222))
