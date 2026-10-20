"""Build dag224: K230's Dag230 with the AX node 236 rebuilt as a fresh right-nested chain whose
atom word is K230's word with the emitter span (contract original_word) replaced by the 224's
canonical_word. All other nodes keep their numbers. Writes dag224_nodes.json and dag224_sites.json."""
import json, sys, os
sys.path.insert(0, os.path.dirname(__file__))
from dagmodel import parse, atoms_of, expand, sites

S = r"C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-merge-article-groups-491e11\31b37d1b-6b02-4181-babf-8c85ac50cb17\scratchpad"
V = S + r"\rocq225\pkg\vendor\k230-rocq\coq\prog"
C = json.load(open(S + r"\intake181\fresh\K224_Construction_2026-10-20\K224_Construction_2026-10-20\portable\theory\emitter_contract.json"))
nodes = parse(V + r"\Dag230.v")
atoms = atoms_of(V + r"\ProgLib230.v")
word = expand(nodes, ("N", 236), atoms)
orig = [("N", x) for x in C["original_word"]]
canon = [("N", x) for x in C["canonical_word"]]
pos = [i for i in range(len(word) - len(orig) + 1) if word[i:i + len(orig)] == orig]
assert pos == [88], pos
new_word = word[:88] + canon + word[88 + len(orig):]
assert all(e[0] != "N" or e[1] in atoms for e in new_word)

N = dict(nodes)
nxt = 301
# right-nested chain: 236 = (w0, c1), c_i = (w_i, c_{i+1}), last chain node = (w_{k-2}, w_{k-1})
chain = [236] + list(range(nxt, nxt + len(new_word) - 2))
for i, n in enumerate(chain):
    a = new_word[i]
    b = ("N", chain[i + 1]) if i + 1 < len(chain) else new_word[i + 1]
    N[n] = (a, b)
nn = max(N) + 1
assert expand(N, ("N", 236), atoms) == new_word
json.dump({"nnodes": nn, "nodes": {str(k): [list(v[0]), list(v[1])] for k, v in sorted(N.items())},
           "word236": [list(e) for e in new_word]}, open(S + r"\k224rocq\dag224_nodes.json", "w"))
st = sites(N, 0, nn)
json.dump(st, open(S + r"\k224rocq\dag224_sites.json", "w"))
print("dag224 nnodes", nn, "word", len(word), "->", len(new_word), "leaves", len(st))
