#!/usr/bin/env python3
"""Read-only source/patch/finite auditor. Never imports or executes Lean/incoming scripts.

All validation is static or finite. A pass is NOT a Lean elaboration/kernel check.
The only output is JSON on stdout. Supply --source-root for another copy of the pin.
"""
from pathlib import Path
import argparse
import hashlib
import json
import math
import re


def require(condition, message="controller audit check failed"):
    if not condition:
        raise ValueError(message)


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def line_counts(text):
    lines = text.splitlines()
    return {"physical": len(lines), "nonblank": sum(bool(s.strip()) for s in lines)}


def apply_patch_in_memory(patch, sources):
    """Strict ordinary unified-diff application; rejects any inexact old context."""
    lines = patch.splitlines(keepends=True)
    i, results = 0, {}
    while i < len(lines):
        require(lines[i].startswith("--- a/"), "controller audit check failed")
        path = lines[i][6:].rstrip("\n")
        require(not Path(path).is_absolute() and ".." not in Path(path).parts, "controller audit check failed")
        require(lines[i + 1] == "+++ b/" + path + "\n", "controller audit check failed")
        require(path not in results, "controller audit check failed")
        i += 2
        original = sources[path].splitlines(keepends=True)
        cursor, result = 0, []
        while i < len(lines) and lines[i].startswith("@@ "):
            h = re.fullmatch(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@.*\n", lines[i])
            require(h, lines[i])
            old_start = int(h[1]) - 1
            old_count = int(h[2] or 1)
            new_start = int(h[3]) - 1
            new_count = int(h[4] or 1)
            require(old_start >= cursor, "controller audit check failed")
            result.extend(original[cursor:old_start])
            require(len(result) == new_start, "controller audit check failed")
            i += 1
            old, new = [], []
            while i < len(lines) and not lines[i].startswith(("@@ ", "--- a/")):
                s = lines[i]
                require(s[:1] in (" ", "+", "-"), s)
                if s[0] in " -":
                    old.append(s[1:])
                if s[0] in " +":
                    new.append(s[1:])
                i += 1
            require(len(old) == old_count and len(new) == new_count, "controller audit check failed")
            require(original[old_start:old_start + old_count] == old, "controller audit check failed")
            result.extend(new)
            cursor = old_start + old_count
        result.extend(original[cursor:])
        results[path] = "".join(result)
    return results


def public_headers(text):
    return {m[1]: m[0] for m in re.finditer(
        r"^theorem ([A-Za-z_][A-Za-z_0-9]*)\b.*? :=", text, re.M | re.S)}


def block(text, name):
    m = re.search(r"^(?:private )?theorem " + re.escape(name) + r"\b", text, re.M)
    require(m, name)
    finish = text.find("\n\n", m.start())
    if finish < 0:
        finish = len(text)
    value = text[m.start():finish]
    return {"start_line": text[:m.start()].count("\n") + 1,
            "end_line": text[:finish].count("\n") + 1,
            **line_counts(value)}


def nat_mod(a, m):
    return a % m if m else a


def auditor_self_tests():
    good = "--- a/x\n+++ b/x\n@@ -1,2 +1,2 @@\n-one\n+ONE\n two\n"
    require(apply_patch_in_memory(good, {"x": "one\ntwo\n"}) == {"x": "ONE\ntwo\n"})
    bad = [good.replace("-one", "-absent"), good.replace("-1,2", "-1,3"),
           good.replace("+1,2", "+2,2"), good.replace("a/x", "a/../x"),
           good.replace("+++ b/x", "+++ b/y"), good + good]
    for patch in bad:
        try:
            apply_patch_in_memory(patch, {"x": "one\ntwo\n"})
        except (ValueError, KeyError):
            continue
        raise ValueError("malformed patch was incorrectly accepted")
    a = "theorem t (h : p) : q := by exact x\n"
    b = "theorem t : q := by exact x\n"
    require(public_headers(a) != public_headers(b))
    require(sha(a) != sha(a.replace("exact x", "exact y")))
    return {"valid_patch_replay": 1, "malformed_patch_rejections": len(bad),
            "public_premise_change_detected": True, "proof_mutation_hash_detected": True}


def finite_checks():
    quotient_cases = 0
    for c in range(1, 13):
        for t in range(1, 13):
            for z in range(c * t):
                a, q = z % c, z // c
                require(a < c and q < t, "controller audit check failed")
                require((a + c * (q % t)) % (c * t) == z, "controller audit check failed")
                quotient_cases += 1

    cardinality_cases = 0
    for p in (2, 3, 5, 7, 11):
        for multiple in range(1, 5):
            c = p * multiple
            for t in range(c):
                for b in range(c):
                    if b % p == 0:
                        continue
                    e = int(t % p == 0)
                    a = (t - e * b) % c
                    require(e <= 1 and 0 < a < c and a % p != 0, "controller audit check failed")
                    require(a % p == (t % p - e * (b % p)) % p, "controller audit check failed")
                    for n in range(5):
                        require(math.gcd(a, p ** n) == 1, "controller audit check failed")
                        cardinality_cases += 1

    interval_cases = 0
    for t in range(1, 25):
        for a in range(t + 1):
            if math.gcd(a, t) != 1:
                continue
            for u in range(t):
                inv = 0 if t == 1 else pow(a, -1, t)
                start = (inv * (u - a * (a - 1) // 2)) % t
                subset = {(start + j) % t for j in range(a)}
                require(len(subset) == a and sum(subset) % t == u, "controller audit check failed")
                interval_cases += 1

    end_to_end_cases = 0
    for c, p, n in ((2, 2, 2), (6, 3, 2), (4, 2, 3), (5, 5, 2)):
        t = p ** n
        modulus = c * t
        require(c % p == 0 and c < t, "controller audit check failed")
        for target in range(modulus):
            for b in range(modulus):
                if b % p == 0:
                    continue
                e = int(target % p == 0)
                residue = (target - e * b) % modulus
                a, u = residue % c, residue // c
                require(0 < a < c and a <= t and math.gcd(a, t) == 1, "controller audit check failed")
                start = (pow(a, -1, t) * (u - a * (a - 1) // 2)) % t
                subset = {(start + j) % t for j in range(a)}
                require(len(subset) == a, "controller audit check failed")
                require((sum(1 + c * x for x in subset) + e * b) % modulus == target, "controller audit check failed")
                end_to_end_cases += 1

    hs_cases = 0
    for b in range(13):
        for k in range(13):
            for m in range(13):
                bm, km, bs = nat_mod(b, m), nat_mod(k, m), nat_mod(b*b, m)
                require(nat_mod(1 + b*k + b*b, m) == nat_mod(
                    nat_mod(nat_mod(1, m) + nat_mod(bm*km, m), m) + bs, m), "controller audit check failed")
                hs_cases += 1
    concrete_hs = []
    for m, bm, km, bs, expected in ((47, 37, 26, 6, 29),
                                  (2011, 1283, 1995, 1091, 674),
                                  (120199, 37435, 114787, 99283, 36379)):
        require(pow(2, 94517, m) == bm and pow(bm, 2, m) == bs, "controller audit check failed")
        actual = (1 + bm*km + bs) % m
        require(actual == expected, "controller audit check failed")
        concrete_hs.append({"modulus": m, "B_residue": bm, "assumed_K_residue": km,
                            "B_square_residue": bs, "Hs_residue": actual})

    # Deliberate failed extensions: maintain these guard counterexamples.
    require(13 % 5 == 8 % 5 and (8 + 5 * (13 // 5)) % 15 != 13, "controller audit check failed")  # a<C0
    require(math.gcd(2, 4) != 1 and 2 % 4 != 0, "controller audit check failed")  # nonzero is insufficient without primality
    require(all((0 - e*0) % 5 == 0 for e in (0, 1)), "controller audit check failed")  # nonzero Boolean translate
    return {"quotient_projection_cases": quotient_cases,
            "coprime_cardinality_cases_including_exponent_zero": cardinality_cases,
            "interval_cases_including_modulus_one": interval_cases,
            "end_to_end_boolean_subset_cases": end_to_end_cases,
            "hs_symbolic_identity_finite_cases_including_modulus_zero": hs_cases,
            "concrete_hs_conditional_residues": concrete_hs,
            "guard_counterexamples": 3, "actual_K_residues_evaluated": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=Path(__file__).resolve().parent.parent / "baseline")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / "manifest.json").read_text(encoding="utf-8"))
    sources = {f["path"]: (args.source_root / f["path"]).read_text(encoding="utf-8")
               for p in manifest["patches"] for f in p["files"]}
    changed = {}
    accounting = []
    headers_total = 0
    for p in manifest["patches"]:
        patch = (here / p["path"]).read_text(encoding="utf-8")
        replacements = apply_patch_in_memory(patch, sources)
        require(set(replacements) == {f["path"] for f in p["files"]}, "controller audit check failed")
        require(not set(changed).intersection(replacements), "controller audit check failed")
        changed.update(replacements)
        for f in p["files"]:
            before, after = sources[f["path"]], replacements[f["path"]]
            require(sha(before) == f["before_sha256"], "controller audit check failed")
            require(sha(after) == f["after_sha256"], "controller audit check failed")
            require(after == (here / "proposed" / Path(f["path"]).name).read_text(encoding="utf-8"), "controller audit check failed")
            for side, text in (("before", before), ("after", after)):
                for count, value in line_counts(text).items():
                    require(f[side + "_" + count] == value, "controller audit check failed")
            require(public_headers(before) == public_headers(after), "controller audit check failed")
            headers_total += len(public_headers(before))
            require(re.findall(r"^import .*", before, re.M) == re.findall(r"^import .*", after, re.M), "controller audit check failed")
            require(re.findall(r"^set_option .*", before, re.M) == re.findall(r"^set_option .*", after, re.M), "controller audit check failed")
            accounting.append({"proposal": p["name"], **f,
                               "physical_saved": f["before_physical"] - f["after_physical"],
                               "nonblank_saved": f["before_nonblank"] - f["after_nonblank"],
                               "added_import_lines": 0, "added_helper_lines": 0})
        additions = "\n".join(s[1:] for s in patch.splitlines() if s.startswith("+") and not s.startswith("+++"))
        require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", additions), "controller audit check failed")

    rel = "Computability/DiophantineConsistency/Lean/DiophantineConsistency/"
    targets = {"ControllerAuxiliaryChoice.lean": ["exists_coprime_cardinality"],
               "CurrentControllerData2011.lean": ["Hs_mod_47", "Hs_mod_2011", "Hs_mod_auxiliary"]}
    declaration_accounting = []
    for filename, names in targets.items():
        for name in names:
            declaration_accounting.append({"file": filename, "declaration": name,
                                          "before": block(sources[rel + filename], name),
                                          "after": block(changed[rel + filename], name)})
    data_before, data_after = sources[rel + "CurrentControllerData2011.lean"], changed[rel + "CurrentControllerData2011.lean"]
    require("hs_mod_of" not in data_after, "controller audit check failed")
    require("attribute [local irreducible] CurrentKernel2011.K B" in data_after, "controller audit check failed")
    references = []
    for f in (args.source_root / rel).glob("*.lean"):
        for n, s in enumerate(f.read_text(encoding="utf-8").splitlines(), 1):
            if re.search(r"\bhs_mod_of\b", s):
                references.append([f.name, n])
    require(len(references) == 4 and {r[0] for r in references} == {"CurrentControllerData2011.lean"}, "controller audit check failed")

    evidence = json.loads((here / "evidence/mathlib_api.json").read_text(encoding="utf-8"))
    mathlib = (here / "evidence" / evidence["local_snapshot"]).read_text(encoding="utf-8")
    require(sha(mathlib) == evidence["source_sha256"], "controller audit check failed")
    encoded = mathlib.encode()
    require(hashlib.sha1(b"blob " + str(len(encoded)).encode() + b"\0" + encoded).hexdigest()
            == evidence["github_blob_sha"], "Git blob SHA mismatch")
    for e in evidence["excerpts"]:
        excerpt = "\n".join(mathlib.splitlines()[e["start_line"]-1:e["end_line"]])
        require(excerpt == e["text"] and sha(excerpt) == e["sha256"], "controller audit check failed")
        require(re.search(r"(?:theorem|lemma) " + re.escape(e["name"]) + r"\b", excerpt), "controller audit check failed")
    output = {"status": "pass", "source_pin": manifest["source_pin"],
              "lean": "NOT COMPILED; no Lean or lake command was invoked",
              "scope": "read-only static patch replay, header/API checks, and finite arithmetic sanity",
              "source_hashes_match_pin_manifest": True,
              "public_theorem_headers_preserved": headers_total,
              "patches_disjoint": True, "accounting": accounting,
              "declaration_accounting": declaration_accounting,
              "deleted_private_helper": {"name": "hs_mod_of", "before": block(data_before, "hs_mod_of"),
                                         "references": references},
              "finite": finite_checks(), "mathlib_evidence_verified": True,
              "self_tests": auditor_self_tests(),
              "optimized_python_safe": "checks use explicit require, not assert"}
    print(json.dumps(output, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
