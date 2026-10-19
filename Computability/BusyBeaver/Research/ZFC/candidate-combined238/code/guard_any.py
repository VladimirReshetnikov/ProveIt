"""Old169/read1 right-neighbor guard, over all valid instruction frames, for ANY
inherited-label table containing state 169 (start 95, dispatch 96, halt 254).

Parameterized re-implementation of Source 101's verification/certify_guard169.py
(intake 172): the instrumentation is copied, the hash pins and the 480-row /
409,691-step constants are replaced by values computed from the given table.
The symbolic engine is imported UNCHANGED from the directory given by --engine
(Source 103's validation/symbolic_runtime.py, the inherited incoming-80 checker).
Usage: guard_any.py --engine DIR --table T --sites S --output OUT.json
"""
import argparse, hashlib, json, sys, time
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("--engine", type=Path, required=True)
ap.add_argument("--table", type=Path, required=True)
ap.add_argument("--sites", type=Path, required=True)
ap.add_argument("--output", type=Path, required=True)
a = ap.parse_args()
assert __debug__ and not sys.flags.optimize
sys.path.insert(0, str(a.engine))
import symbolic_runtime as s  # noqa: E402

table = s.r.table(a.table)
sites = json.loads(a.sites.read_text())
working = {q for q, _ in table}
assert 169 in working and 95 in working and 96 in working and 254 not in working
assert set(table) == {(q, b) for q in working for b in (0, 1)}
assert len(sites) == 6455
lemmas, blocks = s.prove_blocks(table)
assert all(169 not in [ev[1][0] for ev in blk["trace"] if ev[0] in ("literal", "unary")]
           for blk in blocks)
assert all(q != 169 for q, _d, _f, _r in lemmas)
assert all(table[169, bit][2] != 169 for bit in (0, 1))

original_step = s.State.step
visits, ctx = [], {}

def inspected_step(state, current_table, current_lemmas, clock, motion):
    state.key()
    if state.q == 169:
        assert state.direction == 1, ("orientation at 169", ctx)
        atom = state.right[0]
        assert atom[0] == "run" and atom[2][0] >= 1
        if atom[1] == 1:
            assert atom[2][0] >= 2, ("169/read1 right-neighbor guard unproved", ctx, state.key())
            visits.append({**ctx, "run_length": atom[2]})
    return original_step(state, current_table, current_lemmas, clock, motion)

t0 = time.monotonic(); records = []; used = set()
s.State.step = inspected_step
try:
    for index, site in enumerate(sites):
        for positive in ((False, True) if site[1] == "CD" else (False,)):
            ctx = {"site_index": index, "positive": positive}
            before = len(visits)
            ans = s.case(table, lemmas, site, positive)
            used.update(ans["rows"])
            records.append({**ctx, "symbolic_steps": ans["symbolic_steps"],
                            "duration": ans["duration"], "guard_visits": len(visits) - before})
            if len(records) % 1000 == 0:
                print("PASS", len(records), "guards; visits", len(visits),
                      round(time.monotonic() - t0, 1), "s", flush=True)
finally:
    s.State.step = original_step
assert len(records) == 8386 and visits

# Exact blank prefix: run to the initial frame, checking the guard on the way.
W = {-6, 176}; pos = 177
for v in [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167:
    pos += 1; W.update(range(pos, pos + v + 1)); pos += v + 1
q, h, ones, boot, nb = 95, 0, set(), 0, 0
while not ((q, h) == (96, -5) and ones == W):
    assert q != 254 and boot < 3_000_000
    b = int(h in ones)
    if q == 169 and b == 1:
        assert h + 1 in ones, ("blank-prefix guard failure", boot); nb += 1
    w, d, q = table[q, b]
    (ones.add if w else ones.discard)(h); h += d; boot += 1

out = {"status": "PASS_UNIVERSAL_RUNTIME_AND_EXACT_BOOT_GUARD",
       "table_sha256": hashlib.sha256(a.table.read_bytes()).hexdigest(),
       "sites_sha256": hashlib.sha256(a.sites.read_bytes()).hexdigest(),
       "engine_sha256": hashlib.sha256(Path(s.__file__).read_bytes()).hexdigest(),
       "driver_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       "cases": len(records), "symbolic_rules": sum(r["symbolic_steps"] for r in records),
       "runtime_rows_used": len(used), "table_rows": len(table),
       "next_one_guard_visits": len(visits),
       "minimum_one_run_constant": min(v["run_length"][0] for v in visits),
       "boot_steps": boot, "boot_guard_visits": nb, "seconds": time.monotonic() - t0}
a.output.write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
