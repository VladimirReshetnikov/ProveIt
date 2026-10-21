#!/usr/bin/env python3
"""Reconstruct and independently audit the schematic MP shortcuts.
Python is a producer/auditor only; Lean/Rocq kernels establish the theorems.
"""
from __future__ import annotations
import argparse, hashlib, json, pathlib, re, difflib

HERE = pathlib.Path(__file__).resolve().parent

def digest(s):
    return hashlib.sha256(s.encode()).hexdigest()

def parse_term(text):
    toks = re.findall(r"wim|v\d+|0|[()]", text)
    def go(i):
        t = toks[i]
        if t != "(":
            return t, i + 1
        assert toks[i + 1] == "wim"
        a, j = go(i + 2)
        b, j = go(j)
        assert toks[j] == ")"
        return (a, b), j + 1
    result, end = go(0)
    assert end == len(toks), (end, toks)
    return result

def renamed(t, prefix):
    if isinstance(t, str):
        return t if t == "0" else prefix + t
    return (renamed(t[0], prefix), renamed(t[1], prefix))

def substitute(t, subst):
    if isinstance(t, str):
        return substitute(subst[t], subst) if t in subst else t
    return (substitute(t[0], subst), substitute(t[1], subst))

def unify(a, b, subst):
    a, b = substitute(a, subst), substitute(b, subst)
    if a == b:
        return True
    def occurs(x, t):
        t = substitute(t, subst)
        return x == t if isinstance(t, str) else occurs(x, t[0]) or occurs(x, t[1])
    if isinstance(a, str) and a != "0":
        if occurs(a, b):
            return False
        subst[a] = b
        return True
    if isinstance(b, str) and b != "0":
        if occurs(b, a):
            return False
        subst[b] = a
        return True
    return (isinstance(a, tuple) and isinstance(b, tuple)
            and unify(a[0], b[0], subst) and unify(a[1], b[1], subst))

def match(pattern, target, subst):
    if isinstance(pattern, str):
        if pattern == "0":
            return target == "0"
        if pattern in subst:
            return subst[pattern] == target
        subst[pattern] = target
        return True
    return (isinstance(target, tuple)
            and match(pattern[0], target[0], subst)
            and match(pattern[1], target[1], subst))

def fmt(t):
    return t if isinstance(t, str) else "(wim " + fmt(t[0]) + " " + fmt(t[1]) + ")"

def read_nodes(source):
    nodes = {}
    for hit in re.finditer(r"private theorem ((?:b|cd)\d+)\b", source):
        name = hit.group(1)
        block = source[hit.start():].split("\n\n", 1)[0]
        header, body = block.split(":=", 1)
        term_match = re.search(r":\s*T (\([\s\S]*\))\s*$", header)
        assert term_match, name
        variables = re.search(r"theorem \w+\s+\(([^)]*) : Nat\)", header).group(1).split()
        nodes[name] = dict(
            name=name, block=block, header=header, body=body,
            term=parse_term(term_match.group(1)), variables=variables,
            guarded=bool(re.search(r"\(hb\d", header)),
            deps=re.findall(r"\b((?:b|cd)\d+) h\b", body))
    return nodes

def shortcut(spec, nodes):
    x, y, z = (nodes[spec[k]] for k in ("major", "minor", "target"))
    assert not x["guarded"] and not y["guarded"], spec
    major, minor = renamed(x["term"], "x"), renamed(y["term"], "y")
    assert isinstance(major, tuple)
    u = {}
    assert unify(major[0], minor, u), spec
    m = {}
    assert match(substitute(major[1], u), z["term"], m), spec
    def resolve(t):
        t = substitute(t, u)
        if isinstance(t, str):
            return "0" if t == "0" else m.get(t, "0")
        return (resolve(t[0]), resolve(t[1]))
    xa = {v: resolve("x" + v) for v in x["variables"]}
    ya = {v: resolve("y" + v) for v in y["variables"]}
    # Independent structural check: the instantiated minor equals the major's
    # antecedent and its consequent equals the entire target schema.
    def instantiate(t, args):
        return args.get(t, t) if isinstance(t, str) else (instantiate(t[0], args), instantiate(t[1], args))
    imajor, iminor = instantiate(x["term"], xa), instantiate(y["term"], ya)
    assert imajor == (iminor, z["term"]), spec
    expr = "(h.mp ({} h {}) ({} h {}))".format(
        x["name"], " ".join(fmt(xa[v]) for v in x["variables"]),
        y["name"], " ".join(fmt(ya[v]) for v in y["variables"]))
    return expr, dict(spec, major_arguments={v: fmt(xa[v]) for v in xa},
                     minor_arguments={v: fmt(ya[v]) for v in ya})

def ordered_closure(roots, edges):
    done, active, order = set(), set(), []
    def visit(n):
        assert n not in active, "cyclic certificate at " + n
        if n in done:
            return
        active.add(n)
        for d in edges[n]:
            visit(d)
        active.remove(n)
        done.add(n)
        order.append(n)
    for root in roots:
        visit(root)
    return order

def generate():
    cfg = json.loads((HERE / "shortcuts.json").read_text())
    source = (HERE / "DomRho8.original.lean").read_text()
    assert digest(source) == cfg["source_sha256"], "upstream source hash mismatch"
    nodes = read_nodes(source)
    edges = {n: d["deps"] for n, d in nodes.items()}
    replacements, certificate = {}, []
    for spec in cfg["shortcuts"]:
        proof, record = shortcut(spec, nodes)
        replacements[spec["target"]] = proof
        edges[spec["target"]] = [spec["major"], spec["minor"]]
        certificate.append(record)
    order = ordered_closure(cfg["roots"], edges)
    blocks = []
    for n in order:
        block = nodes[n]["block"]
        if n in replacements:
            block = nodes[n]["header"] + ":=\n  " + replacements[n]
        block = block.replace(
            "(show T 0 from by simpa only [wim00] using (b38 h 0 0 0 0))", "h.truth")
        block = block.replace(
            "(show T 0 from by simpa only [wim00] using (cd0 h 0 0 0 0 (Nat.zero_le _)))",
            "h.truth")
        block = block.replace(":= by\n  simpa only [wim00] using ", ":=\n  ")
        block = block.replace("Nat.le_refl", "L.refl").replace("Code254.rho8", "rho8")
        block = re.sub(r"\bNat\b", "A", block)
        block = re.sub(r"\b0\b", "τ", block).replace("≤", "≼")
        blocks.append(block)
    body = "\n\n".join(blocks) + "\n\n"
    # No numerical arithmetic, zero identity, or hidden bottom case remains.
    assert all(token not in body for token in ("Nat.", "wim00", "zero_le", "Code254", "omega"))
    core = (HERE / "templates/core-prefix.txt").read_text() + body + (HERE / "templates/core-suffix.txt").read_text()
    adapter = (HERE / "templates/adapter.txt").read_text()
    for text in (core, adapter):
        assert not re.search(r"(?m)^\s*(axiom|sorry|admit)\b", text)
        assert "native_decide" not in text
    metrics = {
        "base_commit": cfg["base_commit"],
        "source_sha256": digest(source),
        "old_bytes": len(source.encode()), "old_lines": len(source.splitlines()),
        "generic_bytes": len(core.encode()), "adapter_bytes": len(adapter.encode()),
        "combined_bytes": len((core + adapter).encode()),
        "generic_lines": len(core.splitlines()), "adapter_lines": len(adapter.splitlines()),
        "original_numbered_helpers": len(nodes), "retained_numbered_helpers": len(order),
        "rho8_numbered_helper_ancestry": len(ordered_closure(cfg["rho8_roots"], edges)),
        "removed_numbered_helpers": sorted(set(nodes) - set(order)),
        "schematic_mp_replacements": len(replacements),
        "truth_alias_reuses": ["b39", "cd47"],
        "generic_sha256": digest(core), "adapter_sha256": digest(adapter),
        "certificate_status": "all schematic MP equations and acyclic dependencies checked",
        "kernel_status": "external build receipts; this Python script is not a proof kernel",
        "shortcuts": certificate,
    }
    return core, adapter, metrics

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=pathlib.Path, help="write repo-layout Lean files under this directory")
    ap.add_argument("--check", action="store_true", help="check exact delivered source bytes")
    args = ap.parse_args()
    core, adapter, metrics = generate()
    if args.check or args.out is None:
        assert core == (HERE / "DominatedImplication.lean").read_text(), "generic source differs"
        assert adapter == (HERE / "DomRho8.adapter.lean").read_text(), "adapter differs"
    if args.out is not None:
        target = args.out / "BusyBeaver/ZFC"
        target.mkdir(parents=True, exist_ok=True)
        (target / "DominatedImplication.lean").write_text(core)
        (target / "DomRho8.lean").write_text(adapter)
        (args.out / "metrics.json").write_text(json.dumps(metrics, indent=2) + "\n")
    print(json.dumps(metrics, indent=2))

if __name__ == "__main__":
    main()
