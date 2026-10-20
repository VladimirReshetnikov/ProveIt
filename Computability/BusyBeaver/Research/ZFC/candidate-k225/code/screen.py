"""Finite screen (Source 103's finite_screen.py case set: every leaf, both decrement guards) that also records executed rows.
Usage: tscreen.py TABLE SITES.json [OUT.json]
Prints failures and per-state used-row summary (which of rows 0/1 ever execute)."""
import json, sys, importlib.util
from pathlib import Path
from collections import defaultdict
RUN = Path(__file__).resolve().parent / "independent_runtime.py"   # Source 103's, see setup_checkers.sh
spec = importlib.util.spec_from_file_location("independent_runtime", RUN)
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
tab = r.table(sys.argv[1])
x = json.load(open(sys.argv[2]))
ss = x["sites"] if isinstance(x, dict) else x
used = defaultdict(set); fail = []; total = 0
for site in ss:
    for pos in ((False, True) if site[1] == "CD" else (False,)):
        regs = [0] * 9
        if pos: regs[site[2]] = 1
        target = r.expected(site, regs, [0])
        actual, steps, tr = r.run(tab, site[0], regs, limit=10000, trace=True)
        for _, q, h, b, w, d, n in tr:
            used[q].add(b)
        good = (actual[0] == 254) if target is None else actual == target[0]
        total += 1
        if not good:
            fail.append(dict(site=site, positive=pos, steps=steps, last=actual[0]))
# boot is not in the case set: states only the startup uses must be kept by the caller
states = {q for q, _ in tab}
summary = dict(cases=total, failed=len(fail), states=len(states),
               unused=sorted(states - set(used)),
               only0=sorted(q for q in used if used[q] == {0}),
               only1=sorted(q for q in used if used[q] == {1}))
print(json.dumps({k: (v if not isinstance(v, list) else (len(v), v[:40])) for k, v in summary.items()}))
if len(sys.argv) > 3:
    json.dump(dict(summary, failures=fail[:200], used={q: sorted(v) for q, v in used.items()}), open(sys.argv[3], "w"))
