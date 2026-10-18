#!/usr/bin/env python3
"""Seed shortened-axiom fine grammars by pruning the existing binary parse.

Exact edited AX words come from the separate logical-rewrite investigation.
This program establishes word identity, grammar closure and finite AST bounds;
it does not establish logical calibration or binary-machine correctness.
"""
import argparse
import difflib
from functools import cache
import json
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fine", type=Path)
    parser.add_argument("variants", type=Path)
    parser.add_argument("seed", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--mask", type=int, action="append")
    parser.add_argument("--generic-edit", action="store_true", help="Permit exact replacements and insertions, in addition to deletions.")
    args = parser.parse_args()
    sys.path.insert(0, str(args.fine / "runtime/code"))
    from audit_fine_grammar import make_vocabulary
    source, terminals, names, allowed, encode = make_vocabulary()
    original = names[76]
    immutable_original = original
    by_ast = {int(ast): names[int(q)] for q, ast in source["sequence_ast_roots"].items()}
    seed = json.loads(args.seed.read_text())
    if seed.get("source_override"):
        assert seed["source_override"]["original_word"] == immutable_original
        original = seed["source_override"]["new_word"]
        by_ast[int(source["sequence_ast_roots"]["76"])] = original
    frozen = {w: (a, b) for w, a, b in seed["rules"]}
    lines = (args.fine / "fine-grammar.txt").read_text().splitlines()
    nr, nroot, _ = map(int, lines[0].split())
    old = {w: (w[:int(k)], w[int(k):]) for k, w, q in map(str.split, lines[1:nr + 1])}
    base_roots = lines[nr + 1:nr + 1 + nroot]
    terminal_rows = lines[nr + 1 + nroot:]
    constraints = (args.fine / "fine-constraints.txt").read_text()
    args.output.mkdir(parents=True, exist_ok=True)
    source_variants = json.loads(args.variants.read_text())
    variants = source_variants.get("variants", [dict(source_variants, mask=source_variants.get("mask", 1000))])
    # A named Boolean-rewrite family need not use the DNE bit-mask schema.
    # Give such records stable directory identifiers without changing their words.
    variants = [dict(v, mask=v.get("mask", 1000 + i)) for i, v in enumerate(variants)]
    if args.mask:
        variants = [v for v in variants if v["mask"] in args.mask]
    results = []
    for variant in variants:
        target = variant["fine_AX"]
        grammar = dict(frozen)
        @cache
        def ep(i):
            if i in by_ast:
                return wp(by_ast[i])
            r = source["ast_dag"][i]
            return (0, 0, 0) if r[0] == "L" else join(ep(r[1]), ep(r[2]))
        @cache
        def wp(w):
            if w in terminals:
                return ep(source["atoms"][terminals[w]]["ast"])
            return join(*(wp(c) for c in grammar.get(w, old.get(w))))
        def join(a, b):
            return 1 + a[0], max(1 + a[0], a[1], b[1]), 1 + max(a[2], b[2])
        def permitted(w, side):
            return w not in terminals or bool(allowed[w] & (1 << side))
        def known(w):
            return w in grammar or w in terminals
        def add(w, a, b):
            assert w == a + b and permitted(a, 0) and permitted(b, 1)
            if w in terminals:
                return w
            if w not in grammar:
                grammar[w] = (a, b)
            return w
        repairs = []
        def repair(w):
            if known(w):
                return w
            # Preserve long unchanged chunks. A small deterministic beam of
            # dictionary parses avoids committing to one unlucky atom boundary.
            vocabulary = sorted((q for q in set(grammar) | set(terminals) if len(q) <= len(w)), key=lambda q: (-len(q), q))
            starts = {}
            for q in vocabulary:
                starts.setdefault(q[0], []).append(q)
            beam = [[] for _ in range(len(w) + 1)]
            beam[0] = [()]
            for i in range(len(w)):
                if not beam[i]:
                    continue
                for q in starts.get(w[i], []):
                    if w.startswith(q, i):
                        j = i + len(q)
                        beam[j].extend(p + (q,) for p in beam[i])
                        beam[j] = sorted(set(beam[j]), key=lambda p: (len(p), p))[:12]
            best = None
            for pieces in beam[-1]:
                pref = [0]
                for p in pieces:
                    pref.append(pref[-1] + len(p))
                @cache
                def chart(i, j):
                    word = w[pref[i]:pref[j]]
                    if known(word):
                        return (0, wp(word), None)
                    options = []
                    for k in range(i + 1, j):
                        a, b = w[pref[i]:pref[k]], w[pref[k]:pref[j]]
                        if not permitted(a, 0) or not permitted(b, 1):
                            continue
                        left, right = chart(i, k), chart(k, j)
                        if left is None or right is None:
                            continue
                        prop = join(left[1], right[1])
                        if prop[1] > 6 or prop[2] > 57:
                            continue
                        options.append((1 + left[0] + right[0], prop, k))
                    return min(options, default=None, key=lambda v: (v[0], v[1][0], v[1][2]))
                plan = chart(0, len(pieces))
                if plan is not None and (best is None or (plan[0], plan[1][0], plan[1][2]) < best[0]):
                    def realize(i, j):
                        word = w[pref[i]:pref[j]]
                        p = chart(i, j)
                        if p[2] is None:
                            return word
                        k = p[2]
                        return add(word, realize(i, k), realize(k, j))
                    # Realize immediately: added valid words only enrich later
                    # dictionary parses, with no mutation of preexisting rows.
                    result = realize(0, len(pieces))
                    repairs.append({"length": len(w), "frontier": len(pieces), "estimated_new_rules": plan[0]})
                    return result
            raise ValueError(("No orientation/zero6-valid dictionary reparse", len(w), w[:80]))
        # Standard exact sequence alignment supplies only deletion intervals.
        matcher = difflib.SequenceMatcher(None, original, target, autojunk=False)
        keep = [False] * len(original)
        operations = matcher.get_opcodes()
        if args.generic_edit:
            emissions = list(original)
            prefixes = [""] * (len(original) + 1)
            for op, i, j, a, b in operations:
                if op == "delete":
                    emissions[i:j] = [""] * (j - i)
                elif op == "replace":
                    emissions[i:j] = [target[a:b]] + [""] * (j - i - 1)
                elif op == "insert":
                    prefixes[i] += target[a:b]
            emissions = [prefixes[i] + c for i, c in enumerate(emissions)]
            emissions[-1] += prefixes[-1]
            assert "".join(emissions) == target
        elif any(op not in ("equal", "delete") for op, *_ in operations):
            # Every DNE target is a subsequence. Greedy alignment is a valid
            # fallback if the general differencer chooses a replacement tie.
            cursor = 0
            for i, c in enumerate(original):
                if cursor < len(target) and c == target[cursor]:
                    keep[i] = True
                    cursor += 1
            assert cursor == len(target)
        else:
            for op, i, j, a, b in operations:
                if op == "equal":
                    keep[i:j] = [True] * (j - i)
        if not args.generic_edit:
            assert "".join(c for c, k in zip(original, keep) if k) == target
            emissions = [c if k else "" for c, k in zip(original, keep)]
        cumulative = [0]
        changed = [0]
        for old_char, emission in zip(original, emissions):
            cumulative.append(cumulative[-1] + len(emission))
            changed.append(changed[-1] + int(emission != old_char))
        def prune(w, offset):
            retained = cumulative[offset + len(w)] - cumulative[offset]
            if retained == 0:
                return ""
            if changed[offset + len(w)] == changed[offset]:
                return w
            revised = "".join(emissions[offset:offset + len(w)])
            if known(revised):
                return revised
            if w in frozen:
                a, b = frozen[w]
                x, y = prune(a, offset), prune(b, offset + len(a))
                if not x:
                    return y
                if not y:
                    return x
                if known(x) and known(y):
                    prop = join(wp(x), wp(y))
                    if permitted(x, 0) and permitted(y, 1) and prop[1] <= 6 and prop[2] <= 57:
                        return add(revised, x, y)
            try:
                return repair(revised)
            except ValueError:
                # A partial atomic implementation may not stand alone. Carry
                # its exact token word upward so a larger interval can reparse.
                return revised
        try:
            result = prune(original, 0)
            assert result == target
            if not known(result):
                repair(result)
            roots = [target if w == original else w for w in seed["roots"]]
            live = set()
            def visit(w):
                if w in terminals or w in live:
                    return
                live.add(w)
                for c in grammar[w]:
                    visit(c)
            for w in roots + [r["word"] for r in seed["routes"]]:
                visit(w)
            reduced = {w: grammar[w] for w in live}
            output = dict(seed)
            output.update(status="ABSTRACT_FINE_SOURCE_REWRITE_ONLY", rules_count=len(live),
                          roots=roots, rules=[[w, *reduced[w]] for w in sorted(live)], properties=[],
                          source_override={"state": 76, "original_word": immutable_original, "new_word": target, "mask": variant["mask"], "rewrite_name": variant.get("name", "dne_mask_%d" % variant["mask"])},
                          seed_construction={"method": "Exact AX edits and dictionary reparse", "net_deleted_tokens": len(original) - len(target), "repairs": repairs})
            directory = args.output / ("mask%02d" % variant["mask"])
            directory.mkdir(exist_ok=True)
            (directory / "seed.json").write_text(json.dumps(output, indent=2) + "\n")
            # The old-rule fallback retains old named AST definitions. The
            # revised AX is an additional expression root with its own rule.
            all_rules = dict(old)
            all_rules.update(reduced)
            input_roots = [target if w == immutable_original else w for w in base_roots]
            text = [f"{len(all_rules)} {len(input_roots)} {len(terminal_rows)}"]
            text += [f"{len(a)} {w} 0" for w, (a, b) in all_rules.items()]
            text += input_roots + terminal_rows
            (directory / "grammar.txt").write_text("\n".join(text) + "\n")
            revised_constraints = constraints.replace("W " + immutable_original + "\n", "W " + target + "\n")
            assert revised_constraints.count("W " + target + "\n") == 1
            (directory / "constraints.txt").write_text(revised_constraints)
            text = [str(len(reduced))] + [f"{len(a)} {w}" for w, (a, b) in reduced.items()]
            text += [str(len(seed["routes"]))] + [r["word"] for r in seed["routes"]]
            (directory / "resume.txt").write_text("\n".join(text) + "\n")
            results.append({"mask": variant["mask"], "rules": len(live), "status": "SEED_CREATED", "directory": str(directory)})
        except (ValueError, KeyError, RecursionError) as exc:
            results.append({"mask": variant["mask"], "status": "SEED_FAILED", "error": repr(exc)})
        print(results[-1], flush=True)
    (args.output / "summary.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
