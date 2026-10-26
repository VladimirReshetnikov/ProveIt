#!/usr/bin/env python3
"""Read-only, stdlib-only static and finite audit; NOT a Lean checker.

Run from any cwd: python path/to/safety/verify_safety.py [--root PACKAGE_DIR].
Only reads bytes and prints JSON. Never invokes Git, Lean, shell commands,
archive members, network services, or an incoming executable.
"""
import argparse
import difflib
import hashlib
import itertools
import json
from pathlib import Path
import re

PIN = "9d9d1123b39927d30363f1dcd53c23f0575c30ee"
BASE_SHA = "aab00b74d13e24bb78dda62c5c5a5fa55990f414821fef7b56d02c8fee675acf"
CANDIDATE_SHA = "b76c4621db790f9bf780a0d68defffcfb8aeba56f6c1f91936edda2c1cc08fa0"
NAMES = ["position_budget", "position_injective"]
NAME = "CurrentControllerPositions2011.lean"
SOURCE = "Computability/DiophantineConsistency/Lean/DiophantineConsistency/" + NAME


def require(ok, label):
    if not ok:
        raise ValueError(label)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def metrics(data):
    return {"sha256": sha(data), "git_blob": hashlib.sha1(
        ("blob %d\0" % len(data)).encode() + data).hexdigest(),
        "physical": len(data.splitlines()),
        "nonblank": sum(bool(x.strip()) for x in data.splitlines()),
        "bytes": len(data)}


def check_static(root):
    manifest = json.loads((root / "manifest.json").read_text())
    baseline = (root / "baseline" / NAME).read_bytes()
    candidate = (root / "candidate" / NAME).read_bytes()
    require(manifest["source_pin"] == PIN, "source pin changed")
    require(manifest["source_path"] == SOURCE, "source path changed")
    require(sha(baseline) == BASE_SHA, "pinned baseline bytes changed")
    require(sha(candidate) == CANDIDATE_SHA, "reviewed candidate bytes changed")
    require(manifest["baseline"] == metrics(baseline), "baseline metrics mismatch")
    require(manifest["candidate"] == metrics(candidate), "candidate metrics mismatch")
    require(manifest["lean_status"] == "UNCOMPILED", "uncompiled status changed")
    require(manifest["new_helpers"] == manifest["new_imports"] == 0,
            "unaccounted helper or import cost")
    require(manifest["withdrawn_optional_branch"] ==
            ["optional_next_lt", "optional_stride_lt", "position_ne_three"],
            "optional-branch withdrawal inventory changed")
    require({p.name for p in (root / "patches").iterdir()} ==
            {"position_budget.patch", "position_injective.patch", "positions_combined.patch"},
            "unreviewed or withdrawn patch in delivered patch directory")
    old, new = baseline.decode(), candidate.decode()
    changes = manifest["changes"]
    require([c["theorem"] for c in changes] == NAMES, "change inventory changed")
    rebuilt = old
    for c in changes:
        before, after = c["before_body"], c["after_body"]
        require(rebuilt.count(before) == 1, "nonunique original body: " + c["theorem"])
        require(len(before.splitlines()) == c["physical_before"], "body count before")
        require(len(after.splitlines()) == c["physical_after"], "body count after")
        rebuilt = rebuilt.replace(before, after)
        exact_patch = "".join(difflib.unified_diff(old.splitlines(True),
            old.replace(before, after).splitlines(True), "a/" + SOURCE, "b/" + SOURCE))
        require((root / c["patch"]).read_text() == exact_patch,
                "individual patch mismatch: " + c["theorem"])
    require(rebuilt == new, "candidate has edits outside two exact proof bodies")
    combined = "".join(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                                          "a/" + SOURCE, "b/" + SOURCE))
    require((root / "patches" / "positions_combined.patch").read_text() == combined,
            "combined patch differs from exact source diff")
    order_count = 0
    for order in itertools.permutations(changes):
        rebuilt = old
        for c in order:
            require(rebuilt.count(c["before_body"]) == 1, "patch order overlap")
            rebuilt = rebuilt.replace(c["before_body"], c["after_body"])
        require(rebuilt == new, "noncommuting proof edits")
        order_count += 1
    require(not re.search(r"\b(?:sorry|admit|axiom|unsafe)\b", new),
            "unchecked proof construct")
    require(old.split("theorem cell_val", 1)[1] == new.split("theorem cell_val", 1)[1],
            "canonical-value/support/cyclic safety tail changed")
    require(manifest["physical_saved"] == manifest["nonblank_saved"] == 4,
            "savings changed")
    refs = {}
    for name, expected in manifest["reference_files"].items():
        data = (root / "reference" / name).read_bytes()
        actual = metrics(data)
        require(all(actual[k] == value for k, value in expected.items()),
                "reference changed: " + name)
        refs[name] = actual["sha256"]
    controller = (root / "reference" / "CurrentControllerData2011.lean").read_text()
    require("def auxiliary : ℕ := 120199" in controller, "fixed auxiliary changed")
    safety = (root / "reference" / "CurrentDummySafety2011.lean").read_text()
    for guard in ["(hj : dummy j = 0)", "(hnext : j.val+1 < N)",
                  "(htime : j.val+s < N)",
                  "(CurrentWordConstruction2011.word a dummy marker) (displacement s) carry digits)",
                  "(CurrentWordConstruction2011.word a (Function.update dummy j 1) marker)",
                  "(displacement s) carry' digits'", "normalized_nonwrap_of_safe"]:
        require(guard in safety, "missing unchanged safety binding: " + guard)
    return {"exact_reconstruction": True, "all_body_edit_orders": order_count,
            "patch_application_contract": "Use combined patch alone for both changes; isolated patches are separate single-edit alternatives against original baseline, not an arbitrary sequential patch set.",
            "unified_patch_sequence_validation": False,
            "complete_file_metrics": {"before": metrics(baseline), "after": metrics(candidate)},
            "helpers_added": 0, "imports_added": 0, "proof_bodies_changed": NAMES,
            "reference_sha256": refs, "safety_module_edited": False}


def finite_checks():
    counts = {"affine_points": 0, "injectivity_pairs": 0, "optional_next": 0,
              "optional_stride": 0, "support_sets": 0, "safe_exponent_triples": 0}
    # Generalized small radices cover empty/singleton orbits and all representatives.
    # The actual fixed auxiliary is checked exhaustively at k=1 and at selected
    # endpoints at larger k, without ever computing the enormous literal kernel.
    for a in [5, 6, 7, 11, 120199]:
        for k in range(5):
            q, n = a ** k, a ** (k + 1)
            values = range(q) if q <= 120199 else sorted({0, 1, 2, q // 2, q - 2, q - 1})
            for v in values:
                p = 2 + (a - 1) * v
                require(v + 1 <= q, "canonical representative assumption")
                require(p + q + a <= n + 3, "position budget finite failure")
                require(p != 3, "position collision with optional cell")
                require(0 < p and p + 1 < n, "physical successor finite failure")
                counts["affine_points"] += 1
            require(0 < q and 4 < a * q, "optional next bound")
            counts["optional_next"] += 1
            for rw in range(k):
                r = a ** rw
                require(r < q and 3 + r < a * q, "optional stride bound")
                counts["optional_stride"] += 1
            sample = list(range(min(q, 12))) + ([q - 1] if q > 12 else [])
            for u in sample:
                for v in sample:
                    require(((2 + (a - 1) * u == 2 + (a - 1) * v) == (u == v)),
                            "affine injectivity failure")
                    counts["injectivity_pairs"] += 1
            subsets = [set(), {0}, {q - 1}, {0, q - 1}, set(sample)]
            for subset in subsets:
                image = {2 + (a - 1) * v for v in subset}
                for epsilon in [0, 1]:
                    support = image | ({3} if epsilon else set())
                    require(len(support) == len(subset) + epsilon, "support cardinality")
                    require(len({x % n for x in support}) == len(support), "cast injectivity")
                    for x in support:
                        require(0 < x and x + 1 < n, "support physical successor")
                        for rw in range(k):
                            require(x + a ** rw < n, "support physical stride")
                    counts["support_sets"] += 1
    # Linear proof obligations also checked on arbitrary bounded q,v,r, so this
    # is not solely a test of power identities on a few fixed exponents.
    affine_abstraction = 0
    for q in range(1, 101):
        for v in range(q):
            require(2 + 120198 * v + q + 120199 <= 120199 * q + 3,
                    "linear budget abstraction")
            require(3 + v < 120199 * q, "linear optional stride abstraction")
            affine_abstraction += 1
    for n in range(2, 13):
        for j in range(n):
            for s in range(n + 2):
                if j + 1 < n and j + s < n:
                    require(4022 <= n * 2011, "minimum word length")
                    require(2999 + 2011 * j <= n * 2011 - 1023,
                            "kernel exponent safety")
                    require(977 + 2011 * (j + s) <= n * 2011 - 1034,
                            "temporal exponent safety")
                    counts["safe_exponent_triples"] += 1
    controls = {
        "auxiliary_2_collides_with_three": 2 + (2 - 1) * 1 == 3,
        "auxiliary_4_breaks_optional_next_at_k0": not (4 < 4 ** 1),
        "wrong_stride_rw_kplus1_fails": not (3 + 120199 ** 1 < 120199 ** 1),
        "epsilon_2_breaks_cardinality_contract": len({3}) != 0 + 2,
        "last_cell_breaks_kernel_margin": not (2999 + 2011 <= 2 * 2011 - 1023),
        "wrapped_temporal_destination_breaks_margin": not (977 + 2011 * 3 <= 3 * 2011 - 1034),
        "already_enabled_dummy_has_zero_increment": (1 - 1) != 1,
    }
    require(all(controls.values()), "a negative-control witness failed")
    return {"counts": counts, "linear_abstraction_pairs": affine_abstraction,
            "retained_candidate_checks": "affine budget and injectivity; other finite cases are unchanged-baseline safety regressions, not restored optional-branch novelty",
            "negative_controls": controls,
            "scope": "Finite arithmetic evidence only; not Lean elaboration or a proof of universal quantifiers."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    result = {"status": "PASS", "source_pin": PIN, "lean_status": "UNCOMPILED",
              "static": check_static(args.root), "finite": finite_checks(),
              "no_source_edits_no_external_execution": True}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
