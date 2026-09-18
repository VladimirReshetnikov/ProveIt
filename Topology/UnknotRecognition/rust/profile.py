"""Timing and phase profile of the Rust binary.  Writes results/profile.json.

Times are measured inside the process (after parsing and validation); the
median of `--repeat` runs is reported.  The phase split (transfer = adding a
crossing and delooping, eliminate = Gaussian elimination) comes from the
binary's own timers.
"""
from __future__ import annotations

import json
import os
import platform
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
FAST = os.path.join(HERE, "..", "fast")
BINARY = os.path.join(HERE, "target", "release", "fastunknot.exe" if os.name == "nt" else "fastunknot")


def run(command, data, *options, timeout=900):
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as handle:
        json.dump(data, handle)
    try:
        p = subprocess.run([BINARY, command, handle.name, *options], capture_output=True, text=True, timeout=timeout)
        return json.loads(p.stdout)
    except subprocess.TimeoutExpired:
        return {"timeout": timeout}
    finally:
        os.unlink(handle.name)


def one_component(strands, word):
    p = list(range(strands))
    for g in word:
        i = abs(g) - 1
        p[i], p[i + 1] = p[i + 1], p[i]
    seen, count = set(), 0
    for s in range(strands):
        if s in seen:
            continue
        count += 1
        while s not in seen:
            seen.add(s)
            s = p[s]
    return count == 1


def random_braid(rng, strands, length):
    while True:
        word = [rng.choice([-1, 1]) * rng.randint(1, strands - 1) for _ in range(length)]
        if one_component(strands, word):
            return {"braid": {"strands": strands, "word": word}}


def main():
    bench = json.load(open(os.path.join(FAST, "results", "benchmark_0.1.json"), encoding="utf-8"))
    words = {(r["family"], r["crossings"]): r["word"] for r in bench["scan_families"] if "word" in r}

    def old(strands, length):
        return {"braid": {"strands": strands, "word": words[f"random {strands}-braid", length]}}

    def example(name):
        return json.load(open(os.path.join(FAST, "examples", name), encoding="utf-8"))

    rows = []

    def record(group, case, command, data, *options, repeat=5):
        r = run(command, data, "--repeat", str(repeat), *options)
        row = {"group": group, "case": case, "options": list(options), **r}
        rows.append(row)
        brief = {k: row.get(k) for k in ("reduced_rank", "status", "method", "seconds", "timeout") if k in row}
        print(group, case, options, brief, flush=True)

    raw = [("conway", example("conway.json")), ("kinoshita_terasaka", example("kinoshita_terasaka.json")),
           ("T(3,11)", {"braid": {"strands": 3, "word": [1, 2] * 11}}), ("braid3_40", old(3, 40)),
           ("braid4_41", old(4, 41)), ("braid6_31", old(6, 31)), ("braid5_36", old(5, 36)),
           ("chain256", {"braid": {"strands": 257, "word": list(range(1, 257))}}),
           ("conway_sum_2", example("conway_sum_2.json"))]
    for case, data in raw:
        record("raw", case, "khovanov", data)
    for case, data in raw:
        if case in ("braid4_41", "braid5_36", "conway_sum_2"):
            record("ablation", case, "khovanov", data, "--tail", "1")
            record("ablation", case, "khovanov", data, "--lifo", "--seconds", "300", repeat=1)
    record("rank", "conway_sum_8", "khovanov", example("conway_sum_8.json"), "--factor")
    rec = [("trefoil", example("trefoil.json")), ("torus_3_5", example("torus_3_5.json")),
           ("hard_unknot_8", example("hard_unknot_8.json")), ("unknot_braid40", example("unknot_braid40.json")),
           ("conway", example("conway.json")), ("kinoshita_terasaka", example("kinoshita_terasaka.json")),
           ("conway_sum_2", example("conway_sum_2.json")), ("conway_sum_3", example("conway_sum_3.json")),
           ("T(3,61)", {"braid": {"strands": 3, "word": [1, 2] * 61}}), ("braid5_36", old(5, 36))]
    for case, data in rec:
        record("recognize", case, "recognize", data, repeat=21)
    # scaling: larger random braid closures, raw scan, budget 300 s each
    rng = random.Random(20260918)
    for strands, length in ((3, 80), (3, 160), (4, 61), (4, 81), (5, 48), (5, 60), (6, 43), (6, 55), (7, 48), (8, 49)):
        data = random_braid(rng, strands, length)
        record("scaling", f"random {strands}-braid, {length} crossings", "khovanov", data, "--seconds", "300", repeat=1)
        rows[-1]["word"] = data["braid"]["word"]
    os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
    with open(os.path.join(HERE, "results", "profile.json"), "w", encoding="utf-8") as handle:
        json.dump({"platform": platform.platform(), "rustc": subprocess.run(["rustc", "--version"], capture_output=True,
                   text=True).stdout.strip(), "rows": rows}, handle, indent=1)


if __name__ == "__main__":
    sys.exit(main())
