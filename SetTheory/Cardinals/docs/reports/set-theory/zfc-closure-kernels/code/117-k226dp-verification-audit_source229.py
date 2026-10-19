#!/usr/bin/env python3
"""Independent boundary audit of K230's four decrement-loop rewrites.

Uses only literal (path, opcode, argument) catalogues. The target arithmetic
is implemented directly from the equations in K230's RM.v, without importing
the source transformer or runtime checker. The unbounded argument is the
two-case local recurrence explained in source229_proof.tex.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def leaf(op, argument):
    return ("leaf", op, argument)


def node(left, right):
    return ("node", left, right)


OLD = node(node(leaf("CD", 6), node(leaf("CI", 5), leaf("CC", 2))), leaf("CI", 5))
NEW = node(leaf("CI", 5), node(leaf("CD", 6), leaf("CC", 2)))


def read_sites(path):
    rows = json.loads(path.read_text())
    sites = {}
    for row in rows:
        if len(row) == 2:
            address, instruction = row
            parts = instruction.split()
            op = {"EInc":"CI", "EDecnz":"CD", "EContinue":"CC", "EBreak":"CB", "EHalt":"CH"}[parts[0]]
            argument = None if op == "CH" else int(parts[1])
            assert len(parts) == (1 if op == "CH" else 2)
        else:
            address, op, argument = row
        assert address and set(address) <= {"0", "1"}
        assert address not in sites
        assert op in {"CI", "CD", "CC", "CB", "CH"}
        if op == "CH":
            assert argument is None
        else:
            assert isinstance(argument, int) and argument >= 0
        sites[address] = (op, argument)
    prefixes = {p[:i] for p in sites for i in range(len(p)+1)}
    def build(p):
        if p in sites:
            assert p+"0" not in prefixes and p+"1" not in prefixes
            return leaf(*sites[p])
        assert p+"0" in prefixes and p+"1" in prefixes, p
        return node(build(p+"0"), build(p+"1"))
    return sites, build("")


def increment(path):
    if not path:
        return ""
    bits = list(path)
    i = len(bits)-1
    while i >= 0 and bits[i] == "1":
        bits[i] = "0"
        i -= 1
    if i >= 0:
        bits[i] = "1"
    return "".join(bits)


def strip(path, bit, count):
    while path and count:
        if path[-1] == bit:
            count -= 1
        path = path[:-1]
    return path


def resolve(sites, instruction_pointer):
    prefix = ""
    maximum = max(map(len, sites))
    for i in range(maximum+1):
        if prefix in sites:
            return prefix
        prefix += instruction_pointer[i] if i < len(instruction_pointer) else "0"
    raise AssertionError("complete finite source tree did not resolve")


def edges(sites, address):
    op, argument = sites[address]
    if op == "CH":
        return {"halt": None}
    if op == "CI":
        targets = {"normal": increment(address)}
    elif op == "CD":
        targets = {"positive": increment(address), "zero": increment(strip(address, "0", 1))}
    elif op == "CC":
        targets = {"continue": strip(address, "1", argument)}
    else:
        targets = {"break": increment(strip(address, "0", argument))}
    return {guard: resolve(sites, target) for guard, target in targets.items()}


def rewrite(tree, prefix="", occurrences=None):
    if occurrences is None:
        occurrences = []
    if tree == OLD:
        occurrences.append(prefix)
        return NEW
    if tree[0] == "leaf":
        return tree
    return node(rewrite(tree[1], prefix+"0", occurrences), rewrite(tree[2], prefix+"1", occurrences))


def block_of(address, roots):
    if address is None:
        return None
    return next((p for p in roots if address.startswith(p)), None)


def symbolic_case(sites, root, entry, n_positive):
    """Affine R6 = n (positive case) or 0; R5 = s, other registers unchanged.

    A pair (coefficient,constant) means coefficient*n+constant. Only the
    first CD6 is executed, so its outcome is justified by n>=1 or n=0.
    """
    r6 = (1, 0) if n_positive else (0, 0)
    added5 = 0
    address = entry
    trace = []
    while True:
        assert address.startswith(root)
        op, argument = sites[address]
        trace.append({"path": address, "op": op, "argument": argument})
        assert op != "CH"
        if op == "CI":
            assert argument == 5
            added5 += 1
            successor = edges(sites,address)["normal"]
        elif op == "CD":
            assert argument == 6
            if r6 == (0, 0):
                successor = edges(sites,address)["zero"]
            else:
                assert n_positive and r6 == (1, 0)
                r6 = (1, -1)
                successor = edges(sites,address)["positive"]
        elif op == "CC":
            assert argument == 2
            successor = edges(sites,address)["continue"]
        else:
            raise AssertionError("unexpected local control operation")
        if successor == entry or not successor.startswith(root):
            return {"guard": "n>=1" if n_positive else "n=0", "steps": len(trace),
                    "trace": trace, "R5_increment": added5, "R6_affine_n": list(r6),
                    "end_kind": "recur" if successor == entry else "return",
                    "end_path": successor}
        assert len(trace) < 8
        address = successor


def audit(old_path, new_path, upstream_path=None):
    old, old_tree = read_sites(old_path)
    new, new_tree = read_sites(new_path)
    roots = []
    expected = rewrite(old_tree, occurrences=roots)
    assert len(roots) == 4
    assert expected == new_tree, "new source differs from exactly the four claimed rewrites"
    assert all(not a.startswith(b) for a in roots for b in roots if a != b)
    original_ast = None
    if upstream_path is not None:
        upstream, upstream_tree = read_sites(upstream_path)
        assert old == upstream and old_tree == upstream_tree
        original_ast = True

    old_outside = {p:v for p,v in old.items() if block_of(p,roots) is None}
    new_outside = {p:v for p,v in new.items() if block_of(p,roots) is None}
    assert old_outside == new_outside
    old_entry = {p: resolve(old,p) for p in roots}
    new_entry = {p: resolve(new,p) for p in roots}
    entrances = {p:[] for p in roots}
    unchanged_edges = 0
    halt_paths = []
    for path in old_outside:
        old_edges, new_edges = edges(old,path), edges(new,path)
        assert old_edges.keys() == new_edges.keys()
        for guard, target in old_edges.items():
            new_target = new_edges[guard]
            old_root, new_root = block_of(target,roots), block_of(new_target,roots)
            assert old_root == new_root
            if old_root is None:
                assert target == new_target
                if target is None:
                    halt_paths.append(path)
                else:
                    unchanged_edges += 1
            else:
                assert target == old_entry[old_root]
                assert new_target == new_entry[new_root]
                entrances[old_root].append({"from":path,"guard":guard})

    records = []
    for root in roots:
        cases = []
        for positive in (False,True):
            old_case = symbolic_case(old,root,old_entry[root],positive)
            new_case = symbolic_case(new,root,new_entry[root],positive)
            for key in ("steps","R5_increment","R6_affine_n","end_kind"):
                assert old_case[key] == new_case[key]
            if positive:
                assert old_case["steps"] == 3 and old_case["end_kind"] == "recur"
                assert old_case["R6_affine_n"] == [1,-1]
            else:
                assert old_case["steps"] == 2 and old_case["end_kind"] == "return"
                assert old_case["end_path"] == new_case["end_path"]
                assert old_case["R6_affine_n"] == [0,0]
            assert old_case["R5_increment"] == 1
            cases.append({"old":old_case,"new":new_case})
        records.append({"root":root,"old_entry":old_entry[root],"new_entry":new_entry[root],
                        "external_entrances":entrances[root],"induction_cases":cases})
    assert resolve(old,"") == resolve(new,"")
    assert block_of(resolve(old,""),roots) is None
    return {
        "status":"PASS",
        "old_sha256":hashlib.sha256(old_path.read_bytes()).hexdigest(),
        "new_sha256":hashlib.sha256(new_path.read_bytes()).hexdigest(),
        "published_K230_sites_AST_match":original_ast,
        "old_site_count":len(old),"new_site_count":len(new),
        "exact_pattern_replacements":len(roots),"unchanged_outside_sites":len(old_outside),
        "unchanged_nonhalting_outside_edges":unchanged_edges,
        "unchanged_halt_paths":halt_paths,
        "external_entrance_edges_to_blocks":sum(map(len,entrances.values())),
        "all_external_entrances_are_block_entries":True,
        "all_natural_register_effect":{"R5_out":"R5_in+R6_in+1","R6_out":0,"other_registers":"unchanged"},
        "all_natural_local_duration_in_RM_leaf_steps":"3*R6_in+2",
        "all_natural_blocks_return_normally_without_halting":True,
        "proof_method":"two affine local cases and induction on R6; exact exterior control-edge audit",
        "scope":"ordinary unbounded register-program equivalence; no new Rocq theorem or binary runtime proof",
        "blocks":records,
    }


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--old",type=Path,required=True)
    p.add_argument("--new",type=Path,required=True)
    p.add_argument("--upstream",type=Path)
    p.add_argument("--output",type=Path,required=True)
    args=p.parse_args()
    result=audit(args.old,args.new,args.upstream)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k!="blocks"},indent=2))


if __name__=="__main__":
    main()
