import json, sys, os
sys.path.insert(0, os.path.dirname(__file__))
from dagmodel import parse, atoms_of, expand, sites

S = r"C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-merge-article-groups-491e11\31b37d1b-6b02-4181-babf-8c85ac50cb17\scratchpad"
V = S + r"\rocq225\pkg\vendor\k230-rocq\coq\prog"
C = json.load(open(S + r"\intake181\fresh\K224_Construction_2026-10-20\K224_Construction_2026-10-20\portable\theory\emitter_contract.json"))
nodes = parse(V + r"\Dag230.v")
atoms = atoms_of(V + r"\ProgLib230.v")
print("nodes", len(nodes), "atoms", len(atoms))
w236 = [e[1] if e[0] == "N" else e for e in expand(nodes, ("N", 236), atoms)]
print("node 236 word length", len(w236))
orig = C["original_word"]; canon = C["canonical_word"]
def find(word, sub):
    return [i for i in range(len(word) - len(sub) + 1) if word[i:i + len(sub)] == sub]
print("original word at", find(w236, orig), "len", len(orig), "canonical len", len(canon))
# which nodes does the emitter span use? (is the chain shared elsewhere?)
users = {}
for n, (a, b) in nodes.items():
    for e in (a, b):
        if e[0] == "N":
            users.setdefault(e[1], []).append(n)
print("users of 236", users.get(236), "users of 237", users.get(237))
st = sites(nodes, 0, 301)
json.dump(st, open(S + r"\k224rocq\dag230_sites.json", "w"))
print("dag230 tree leaves", len(st))
