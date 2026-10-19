"""Canonical renumbering (Sources 101-103 rule): start 95 -> 0, other states in sorted
order, halt 254 -> N. Writes '#! start 0' table and renumbering.json.
Usage: canon.py OLD.tm OUT.tm RENUM.json"""
import json, sys, hashlib
from tm import load
T = load(sys.argv[1]); S = sorted({q for q, _ in T})
order = [95] + [q for q in S if q != 95]
ren = {q: i for i, q in enumerate(order)}; ren[254] = len(order)
rows = sorted(((ren[q], b), (w, d, ren[r])) for (q, b), (w, d, r) in T.items())
data = "#! start 0\n" + "".join(f"{q} {b} {w} {d} {r}\n" for (q, b), (w, d, r) in rows)
open(sys.argv[2], "w", newline="\n").write(data)
json.dump({"old_to_canonical": {str(k): v for k, v in ren.items()},
           "canonical_to_old": {str(v): k for k, v in ren.items()},
           "start": 0, "dispatcher": ren[96], "halt": ren[254]}, open(sys.argv[3], "w"), indent=2)
print("states", len(order), "dispatcher", ren[96], "halt", ren[254],
      "sha256", hashlib.sha256(data.encode()).hexdigest())
