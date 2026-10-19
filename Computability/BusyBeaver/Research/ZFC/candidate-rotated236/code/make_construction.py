"""Write construction.json: every stage from the 240-state candidate to this table,
with exact row edits, deleted states and SHA-256 of each table (inherited labels)."""
import hashlib
import json
import sys

sys.path.insert(0, __file__.rsplit("code", 1)[0] + "code")
from tm import load  # noqa: E402

STAGES = [
    ("rotation240", "../candidate-composed237/ingredients/rotation240_old.tm", "the 240-state candidate (Source 80)"),
    ("boundary240", "../candidate-composed237/ingredients/boundary240_old.tm",
     "Source 103: reparenthesized register source (DAG 225 -> 224 nodes) with its repaired decoder"),
    ("boundary239", "../candidate-composed237/ingredients/boundary239_old.tm",
     "Source 103: split 218 by the bit behind the head; reuse 223; merge the other role into 179"),
    ("combined238", "../candidate-combined238/zfc_combined238_old.tm",
     "Sources 101/102: delayed erasure, fold 169 into 80 with helper 91/1 (composition: batch-172 intake)"),
    ("composed237", "ingredients/composed237_old.tm",
     "Source 106: fold 235 into 98 with helper 240/1"),
    ("rotated237", "ingredients/rotated237_old.tm",
     "Source 112: closed source rotation (A,(B,C)) -> ((A,B),C), four decoder rows; 224 nodes kept"),
    ("rotated236", "zfc236_old.tm",
     "Source 112: fold 223 into 182 by the bit to its left (rows 182/0, 182/1)"),
]


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


out, prev = {"convention": "inherited labels: start 95, dispatcher 96, halt 254; row = [write, move, next]",
             "stages": []}, None
for name, path, what in STAGES:
    T = load(path)
    st = {"stage": name, "file": path, "sha256": sha(path), "working_states": len({q for q, _ in T}),
          "rows": len(T), "description": what}
    if prev:
        P = prev
        st["deleted_states"] = sorted({q for q, _ in P} - {q for q, _ in T})
        st["added_states"] = sorted({q for q, _ in T} - {q for q, _ in P})
        st["changed_rows"] = [{"row": f"{q}/{b}", "old": list(P[(q, b)]), "new": list(T[(q, b)])}
                              for (q, b) in sorted(set(P) & set(T)) if P[(q, b)] != T[(q, b)]]
    out["stages"].append(st)
    prev = T
base, final = load(STAGES[0][1]), load(STAGES[-1][1])
out["net_from_rotation240"] = {
    "deleted_states": sorted({q for q, _ in base} - {q for q, _ in final}),
    "retained_rows_changed": sum(1 for k in set(base) & set(final) if base[k] != final[k]),
    "retained_rows_unchanged": sum(1 for k in set(base) & set(final) if base[k] == final[k]),
}
out["canonical"] = {"file": "zfc236.tm", "sha256": sha("zfc236.tm"),
                    "start": 0, "dispatcher": 84, "halt": 236}
out["source"] = {"file": "sites_logical.json", "sha256": sha("sites_logical.json"),
                 "leaves": 6455, "distinct_subtrees": 224, "max_depth": 49, "max_zero_run": 6}
json.dump(out, open("construction.json", "w", newline="\n"), indent=1)
print(json.dumps(out["net_from_rotation240"]), [ (s["stage"], s["working_states"], len(s.get("changed_rows", []))) for s in out["stages"]])
