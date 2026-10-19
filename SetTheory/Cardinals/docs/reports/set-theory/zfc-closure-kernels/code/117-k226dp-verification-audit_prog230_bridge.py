#!/usr/bin/env python3
"""Parse K230's literal Rocq program and compare both JSON catalogues.

This is deliberately a small, fail-closed parser for the concrete syntax in
Prog230.v, not a Rocq evaluator. It checks the manifest hash, the exact edge
translation, root, node count, default, initial registers, and every expanded
leaf. It does not import a code generator or the candidate's engine checker.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def no_comments(text):
    result = []
    position = depth = 0
    while position < len(text):
        if text.startswith("(*", position):
            depth += 1
            position += 2
        elif text.startswith("*)", position):
            assert depth > 0
            depth -= 1
            position += 2
            if depth == 0:
                result.append(" ")
        else:
            if depth == 0:
                result.append(text[position])
            position += 1
    assert depth == 0
    return "".join(result)


def compact(text):
    return re.sub(r"\s+", "", text)


def unique(pattern, text):
    matches = re.findall(pattern, text, flags=re.S)
    assert len(matches) == 1, (pattern, len(matches))
    return matches[0]


def table_from_rocq(source):
    text = no_comments(source)
    conversion = unique(r"Definition\s+cv\s*\(e\s*:\s*cedge\)\s*:\s*edge\s*:=\s*(.*?\bend)\s*\.", text)
    assert compact(conversion) == compact("""
      match e with
      | CN m => ENode (N.to_nat m)
      | CI r => EInc r
      | CD r => EDecnz r
      | CB k => EBreak k
      | CC k => EContinue k
      | CH => EHalt
      end
    """)
    definition = unique(r"Definition\s+p230\s*:\s*prog\s*:=\s*(\{\|.*?\|\})\.", text)
    assert compact(definition) == compact("""
      {| nodes := fun n => let '(a,b) := nth n p230_tab (CH,CH) in (cv a,cv b);
         root := 0;
         nnodes := 5124 |}
    """)
    registers = unique(r"Definition\s+R0\s*:\s*regs\s*:=\s*(.*?)\.", text)
    assert compact(registers) == compact("upd (upd regs0 0 3) 4 3")
    body = unique(r"Definition\s+p230_tab\s*:\s*list\s*\(cedge\s*\*\s*cedge\)\s*:=\s*\[(.*?)\]\.", text)
    tokens = re.findall(r"[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[(),;]", body)
    assert "".join(tokens) == compact(body), "unexpected syntax in literal table"
    position = 0

    def expect(token):
        nonlocal position
        assert position < len(tokens) and tokens[position] == token
        position += 1

    def edge():
        nonlocal position
        tag = tokens[position]
        position += 1
        assert tag in {"CN", "CI", "CD", "CB", "CC", "CH"}
        if tag == "CH":
            return tag, None
        assert re.fullmatch(r"[0-9]+", tokens[position])
        argument = int(tokens[position])
        position += 1
        return tag, argument

    result = []
    while position < len(tokens):
        expect("(")
        left = edge()
        expect(",")
        right = edge()
        expect(")")
        result.append((left, right))
        if position < len(tokens):
            expect(";")
    assert len(result) == 5124
    return result


def expand(table):
    active = set()
    reached = set()
    leaves = []
    node_visits = 0

    def descend(index, path):
        nonlocal node_visits
        assert 0 <= index < len(table)
        assert index not in active, "cycle in literal table"
        active.add(index)
        reached.add(index)
        node_visits += 1
        for bit, (tag, argument) in zip("01", table[index]):
            new_path = path + bit
            if tag == "CN":
                descend(argument, new_path)
            else:
                leaves.append((new_path, tag, argument))
        active.remove(index)

    descend(0, "")
    assert reached == set(range(len(table)))
    return leaves, node_visits


def json_sites(path):
    aliases = {"EInc":"CI", "EDecnz":"CD", "EBreak":"CB", "EContinue":"CC", "EHalt":"CH"}
    result = []
    seen = set()
    for row in json.loads(path.read_text()):
        assert isinstance(row, list)
        if len(row) == 2:
            address, instruction = row
            parts = instruction.split()
            tag = aliases[parts[0]]
            assert len(parts) == (1 if tag == "CH" else 2)
            argument = None if tag == "CH" else int(parts[1])
        else:
            assert len(row) == 3
            address, tag, argument = row
        assert isinstance(address, str) and address and set(address) <= {"0", "1"}
        assert address not in seen
        seen.add(address)
        assert tag in {"CI", "CD", "CB", "CC", "CH"}
        if tag == "CH":
            assert argument is None
        else:
            assert isinstance(argument, int) and not isinstance(argument, bool) and argument >= 0
        result.append((address, tag, argument))
    return result


def audit(repo, working):
    manifest_path = repo / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    source_path = repo / "coq/tm/Prog230.v"
    sites_path = repo / "machine/sites230.json"
    assert sha(source_path) == manifest["local_files"]["coq/tm/Prog230.v"]
    assert sha(sites_path) == manifest["sites_sha256"]
    assert sha(repo / "coq/tm/RM.v") == manifest["local_files"]["coq/tm/RM.v"]
    source = source_path.read_text()
    assert manifest["sites_sha256"] in source.split("*)", 1)[0]
    table = table_from_rocq(source)
    expanded, node_visits = expand(table)
    upstream = json_sites(sites_path)
    normalized = json_sites(working)
    assert expanded == upstream, "literal Rocq program differs from published JSON"
    assert expanded == normalized, "normalized working source differs from literal Rocq program"
    assert len(expanded) == 5125
    max_depth = max(len(row[0]) for row in expanded)
    assert max_depth < 5124 + 1, "insufficient walk fuel"
    canonical = json.dumps(expanded, separators=(",", ":")).encode()
    return {
        "status":"PASS",
        "method":"independent fail-closed concrete-syntax parser and full rooted-tree expansion",
        "manifest_sha256":sha(manifest_path),
        "Prog230_v_sha256":sha(source_path),
        "RM_v_sha256":sha(repo / "coq/tm/RM.v"),
        "published_sites_sha256":sha(sites_path),
        "working_sites_sha256":sha(working),
        "canonical_normalized_leaf_list_sha256":hashlib.sha256(canonical).hexdigest(),
        "literal_cv_mapping_verified":True,
        "literal_root":0,
        "literal_nnodes":5124,
        "literal_out_of_range_default":["CH","CH"],
        "literal_initial_registers_0_to_8":[3,0,0,0,3,0,0,0,0],
        "reachable_node_count":5124,
        "node_visits_during_expansion":node_visits,
        "expanded_leaf_count":len(expanded),
        "maximum_leaf_depth":max_depth,
        "opcode_counts":dict(sorted(Counter(row[1] for row in expanded).items())),
        "every_node_reachable":True,
        "no_cycles":True,
        "walk_fuel_sufficient_for_every_pointer":True,
        "ordered_expansion_exactly_equals_published_JSON":True,
        "ordered_expansion_exactly_equals_working_JSON":True,
        "scope":"exact source-object correspondence; does not rebuild or extend Rocq proofs",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo",type=Path,required=True)
    parser.add_argument("--working",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args = parser.parse_args()
    result = audit(args.repo,args.working)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
