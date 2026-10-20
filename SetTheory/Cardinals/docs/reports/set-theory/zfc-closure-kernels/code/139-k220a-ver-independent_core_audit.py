#!/usr/bin/env python3
"""Independent literal parsing, finite-window induction, local diamonds and startup.

Uses no modules or receipts from the construction packet. The finite-window
domain contains arbitrary exterior bits at every shift, making its reachable
contexts an overapproximation of every binary tape, not a finite-test sample.
"""
from pathlib import Path
from collections import deque
import argparse
import hashlib
import json
import time

PINS = {
    "baseline": (
        "4466ec4f947a9c5112397c30ca25b0e70e3ac39ee54878b3e4493a0297d732e4",
        "f80c57e800d4f999d9b4902a8e96bd36d1b6180b3ad322ca8ed0ab67b47f2a5f"),
    "row103": (
        "d096503d36f677f449367155a3e95cc87865984ad1268801326ea95d5ecb2015",
        "df5412edbdb22a53dc40f21d55c12c911c167c96d586962c54f3b3c7987fcc4a"),
    "row157": (
        "201977820ab5533ba910a0ed050970091c9e8e32778df76f8341343f664adb48",
        "93b6917ebf20d7290c7785cc0a4e0ba0939dc60ec12e5edce0fecacf269b7d5f"),
    "both": (
        "e946f3e80febc4a993ed2c7352b18e1aec46d21e331f08f067212cc2ca55ac5e",
        "7114373310dde3d1447a73b6e1a40bbdfb2c8c3c138a3631a4bd2a132c66daa9"),
}
SOURCE_PIN = "837e92d7b1c107330f160f654f6c36ff0b03dfbf6bc2b89c6f782eb7db4c4ce7"


def require(x, msg):
    if not x:
        raise RuntimeError(msg)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def parse(p, terminal):
    t, starts = {}, []
    for line in p.read_text("ascii").splitlines():
        if line.startswith("#! start "):
            starts.append(int(line.removeprefix("#! start ")))
        elif line and not line.startswith("#"):
            q, r, w, d, z = line.split()
            q, r, w, z = map(int, (q, r, w, z))
            require((q, r) not in t and r in (0, 1) and w in (0, 1)
                    and d in ("L", "R"), "Malformed or duplicate row")
            t[q, r] = w, (-1 if d == "L" else 1), z
    qs = {q for q, r in t}
    require(starts == [0] and len(qs) == 220 and terminal not in qs, "State census")
    require(set(t) == {(q, r) for q in qs for r in (0, 1)}, "Total binary table")
    require({z for w, d, z in t.values()} - qs == {terminal}, "Unique terminal")
    return t


def abstract_post(t, q, word):
    w, d, z = t[q, word[5]]
    changed = word[:5] + bytes([w]) + word[6:]
    shifted = changed[1:] if d == 1 else changed[:-1]
    return z, tuple((shifted + bytes([bit])) if d == 1
                    else (bytes([bit]) + shifted) for bit in (0, 1))


def whole_window_run(t, q, word, ticks):
    tape, head = bytearray(word), 5
    for _ in range(ticks):
        require(q != 254 and 0 <= head < 11, "Interior halt or exterior read")
        w, d, q = t[q, tape[head]]
        tape[head] = w
        head += d
    require(q != 254, "Unexpected endpoint halt")
    return q, head, bytes(tape)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--packet", type=Path, required=True)
    ap.add_argument("--baseline", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    a = ap.parse_args()
    began = time.monotonic()
    require(sha(a.packet / "machine/sites220.json") == SOURCE_PIN, "Source pin")
    require((a.packet / "machine/sites220.json").read_bytes()
            == (a.baseline / "machine/sites220.json").read_bytes(), "Source equality")
    baseline = parse(a.baseline / "machine/k220.native.tm", 254)
    # Start accepts all 2^11 bit windows. Shift nondeterministically introduces
    # either exterior bit; this is sound for arbitrary infinite binary tapes.
    initial = {bytes((n >> k) & 1 for k in range(11)) for n in range(2048)}
    contexts = {q: set() for q, _ in baseline}
    contexts[254] = set()
    contexts[0] = set(initial)
    queue = deque((0, word) for word in initial)
    while queue:
        q, word = queue.popleft()
        if q == 254:
            continue
        z, successors = abstract_post(baseline, q, word)
        for nxt in successors:
            if nxt not in contexts[z]:
                contexts[z].add(nxt)
                queue.append((z, nxt))
    require(contexts[0] == initial, "Initial tapes were constrained")
    for q in contexts:
        if q == 254:
            continue
        for word in contexts[q]:
            z, successors = abstract_post(baseline, q, word)
            require(all(nxt in contexts[z] for nxt in successors), "Noninductive window")
    count = sum(len(words) for q, words in contexts.items() if q != 254)
    require(count == 91337, "Unexpected inductive context count")
    require(all(word[4] == 1 for word in contexts[103]), "State103 left-bit lemma")
    records = []
    for name in PINS:
        folder = a.baseline / "machine" if name == "baseline" else a.packet / "machine" / name
        nf, cf = folder / "k220.native.tm", folder / "k220.tm"
        require((sha(nf), sha(cf)) == PINS[name], "Table SHA pin " + name)
        native, canonical = parse(nf, 254), parse(cf, 220)
        order, mapping = [0], {0: 0}
        for q in order:
            for bit in (0, 1):
                z = native[q, bit][2]
                if z != 254 and z not in mapping:
                    mapping[z] = len(mapping)
                    order.append(z)
        require(len(order) == 220, "Graph reachability " + name)
        mapping[254] = 220
        require(canonical == {(mapping[q], r): (w, d, mapping[z])
                              for (q, r), (w, d, z) in native.items()}, "Canonical bijection")
        edits = {key: value for key, value in native.items() if baseline[key] != value}
        expected = {}
        if name in ("row103", "both"):
            expected[103, 1] = (0, -1, 142)
        if name in ("row157", "both"):
            expected[157, 1] = (1, -1, 187)
        require(edits == expected, "Exact edits " + name)
        hist = {}
        for q, words in contexts.items():
            if q == 254:
                continue
            for word in words:
                row = (q, word[5])
                if row not in expected:
                    require(native[row] == baseline[row], "Nonlocal rewrite")
                    durations = (1, 1)
                elif q == 103 or word[4] == 0:
                    durations = (2, 2)
                else:
                    durations = (1, 3)
                if row in expected:
                    left = whole_window_run(baseline, q, word, durations[0])
                    right = whole_window_run(native, q, word, durations[1])
                    require(left == right, "Positive whole-tape macro mismatch")
                hist[durations] = hist.get(durations, 0) + 1
        # Compute expected whole blank tape independently from the physical
        # register frame, rather than using any delivered startup receipt.
        expected_ones = {-6, 176}
        cursor = 177
        for number in [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167:
            cursor += 1
            for pos in range(cursor, cursor + number + 1):
                expected_ones.add(pos)
            cursor += number + 1
        ones, q, head = set(), 0, 0
        for _ in range(409835):
            require(q != 254, "Premature blank halt")
            w, d, q = native[q, int(head in ones)]
            ones.add(head) if w else ones.discard(head)
            head += d
        require((q, head, ones) == (84, -5, expected_ones), "Complete blank tape")
        require(len(ones) == 351 and mapping[84] == 22, "Frame metadata")
        records.append(dict(name=name, native_sha256=sha(nf), canonical_sha256=sha(cf),
                            working_states=220, rows=440, graph_reachable=220,
                            changed_rows=[list(k) for k in sorted(edits)],
                            positive_block_histogram=[[x, y, n] for (x, y), n in sorted(hist.items())],
                            startup_steps=409835, startup_state=84, startup_head=-5,
                            startup_ones=351, whole_tape_equality=True))
    out = dict(status="INDEPENDENT_LITERAL_AND_ALL_TAPE_CORE_AUDIT_PASS",
               source_sha256=SOURCE_PIN, inductive_nonhalting_contexts=count,
               initial_unrestricted_windows=2048, radius=5,
               state103_universal_left_bit=1, records=records,
               scope="Exact identities, BFS bijections, complete blank startup and positive "
                     "all-tape common-endpoint blocks for baseline plus all three variants. "
                     "No new logical calibration or proof-assistant endpoint.",
               seconds=time.monotonic() - began, auditor_sha256=sha(Path(__file__)))
    a.output.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
