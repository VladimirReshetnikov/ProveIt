#!/usr/bin/env python3
"""Exact closed-macro binding for DR215; install beside common/source_language."""
from pathlib import Path
import json
import sys, argparse, hashlib, tempfile
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'vendor'))
import source_language as sl

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def pinned(root, relative):
    paths = {
        'inputs/st215.sites.json': ('baseline/st215.sites.json', '212cf0ffde43c1cc22c183dd8bf0b3a699396f96c9942ee92a7cc372cd273ca9'),
        'source/dr215.sites.json': ('baseline/dr215.sites.json', '74d21758da7e932de766bee079adf11a7917c03a1957b1111abc6463d70eb332')}
    name, digest = paths[relative]
    raw = (root / name).read_bytes()
    require(sha(raw) == digest, 'Wrong pinned source: ' + name)
    return raw

def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n')

def cli(run):
    p = argparse.ArgumentParser(description=run.__doc__)
    p.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument('--work', type=Path)
    a = p.parse_args()
    work = a.work or Path(tempfile.mkdtemp(prefix='dr215-macro-'))
    print(json.dumps(run(a.root, work), indent=2))


def word(text):
    return [(s[:2], int(s[2:])) for s in text.split()]


def run(root, work):
    """Check the literal old/new rho6 words and both renamed closed loads."""
    root, work = Path(root), Path(work)
    oldraw = pinned(root, "inputs/st215.sites.json")
    newraw = pinned(root, "source/dr215.sites.json")
    old, new = json.loads(oldraw), json.loads(newraw)
    sl.tree(old)
    sl.tree(new)
    og, _ = sl.graph_arithmetic(old)
    ng, _ = sl.graph_arithmetic(new)
    require(og == sl.graph_intervals(old), "Old CFG disagreement")
    require(ng == sl.graph_intervals(new), "New CFG disagreement")

    # Literal inherited closed load: data registers 1,2; work registers 6,7;
    # only the indicated parameter register is read and then restored.
    load = word("CD1 CI6 CC2 CD2 CI1 CC2 CD1 CI7 CI6 CC3 CD6 CI7 "
                "CD6 CI1 CC2 CC3 CD7 CI2 CC2 CD3 CI1 CI6 CC3 CD6 CI3 CC2")
    rename = lambda w, r: [(op, r if op in ("CI", "CD") and k == 3 else k)
                           for op, k in w]
    implication = word("CD2 CI7 CD6 CB1 CD7 CI6 CC2 CC3 CD7 CI2 CC2 "
                       "CD1 CI7 CI6 CC3 CD6 CI7 CD6 CI1 CC2 CC3 CD7 "
                       "CI1 CI1 CI1 CI1 CC2")
    macros = {"a": rename(load, 4), "b": rename(load, 5), "c": load,
              "I": implication, "Q": implication + word("CI1 CI1"),
              "F": load[:19] + word("CI1")}
    words = ("aacQFIQFIcI", "aabQFIQFIbI")
    variants = []
    for rows, graph, postfix in zip((old, new), (og, ng), words):
        expected = sum((macros[c] for c in postfix), [])
        require([tuple(r[1:]) for r in rows[887:1170]] == expected,
                "Literal rho6 macro word mismatch")
        lo, spans = 887, []
        for token in postfix:
            hi = lo + len(macros[token])
            require(all(lo <= target <= hi for i in range(lo, hi)
                        for target in graph[i][1]), "Macro has a nonlocal exit")
            spans.append({"macro": token, "span": [lo, hi]})
            lo = hi
        require(lo == 1170, "Wrong rho6 end")
        variants.append({"postfix": postfix, "macro_spans": spans,
                         "literal_word_and_local_exits": True})

    changed = [i for i, (x, y) in enumerate(zip(old, new)) if x != y]
    require(len(old) == len(new) == 4732, "Wrong source length")
    require(changed == [958, 963, 1136, 1141], "Unexpected changed leaves")
    require([g[1] for g in og] == [g[1] for g in ng], "Changed control flow")
    for lo, hi in ((939, 965), (1117, 1143)):
        for i in range(lo, hi):
            op, reg = old[i][1:]
            require(new[i] == [old[i][0], op,
                    5 if op in ("CI", "CD") and reg == 3 else reg],
                    "Load is not the exact register-3-to-5 renaming")
            effect = list(og[i][0])
            if len(effect) == 2 and effect[1] == 3:
                effect[1] = 5
            require(ng[i] == [effect, og[i][1]], "Wrong renamed load effect")

    def expression(postfix):
        stack = []
        for c in postfix:
            if c in "abcF":
                stack.append(c)
            else:
                y, x = stack.pop(), stack.pop()
                stack.append([c, x, y])
        require(len(stack) == 1, "Malformed postfix expression")
        return stack[0]

    def rho6(c):
        return ["I", ["I", ["Q", "a", ["I", ["Q", "a", c], "F"]], "F"], c]

    require(expression(words[0]) == rho6("c"), "Wrong old expression")
    require(expression(words[1]) == rho6("b"), "Wrong new expression")
    result = {
        "status": "EXACT_RHO6_CLOSED_MACRO_BINDING_PASS",
        "old_source_sha256": sha(oldraw), "new_source_sha256": sha(newraw),
        "rho6_span": [887, 1170], "parameters": {"a": 4, "b": 5, "c": 3},
        "changed_source_ordinals": changed, "variants": variants,
        "old_expression": expression(words[0]),
        "new_expression": expression(words[1]),
        "scope": "Exact finite binding to inherited all-natural load and constructor contracts; not an independent runtime or TM calibration proof.",
    }
    write_json(work / "rho6-macro-binding.json", result)
    return result


if __name__ == "__main__":
    cli(run)
