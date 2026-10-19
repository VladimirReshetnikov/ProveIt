#!/usr/bin/env python3
"""Independent sparse complete-support replay of search_blank.cpp discoveries."""
from __future__ import annotations
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
from safe_start import logical_root_safe, stack_certificate, classify

PHYSICAL = (6,2,0,4,3,7,8,5,1)


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        state, bit, write, move, target = line.split()
        state, bit, write, target = map(int, (state, bit, write, target))
        if bit not in (0,1) or write not in (0,1) or move not in ("L","R"):
            raise ValueError("Invalid binary row")
        if (state,bit) in table:
            raise ValueError("Duplicate binary row")
        table[state,bit] = write, (-1 if move=="L" else 1), target
    states = {state for state,bit in table}
    if set(table) != {(state,bit) for state in states for bit in (0,1)}:
        raise ValueError("Incomplete row set")
    if not {target for write,move,target in table.values()} <= states | {254}:
        raise ValueError("Undeclared target")
    return table


def verify(table, hit):
    ones = set()
    head, state = 0, hit["start"]
    for step in range(hit["steps"]):
        if state==254:
            raise ValueError(f"Premature halt at {step}")
        write,move,target = table[state, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += move
        state = target
    if (head,state) != (hit["head"],hit["state"]):
        raise ValueError("Dense/sparse endpoint mismatch")
    if state!=96 or hit["header"]-head<40 or len(hit["values"])<10:
        raise ValueError("Invalid root dimensions")
    expected = {head-1,hit["header"]}
    cursor = hit["header"]+1
    for value in hit["values"]:
        if not isinstance(value,int) or value<0:
            raise ValueError("Invalid register block")
        expected.update(range(cursor+1,cursor+value+2))
        cursor += value+2
    if ones != expected:
        raise ValueError("Complete infinite-tape support differs from reconstructed frame")
    logical = [hit["values"][r] for r in PHYSICAL]
    if logical != hit["logical"] or not logical_root_safe(logical):
        raise ValueError("Logical Safe certificate rejected")
    return dict(status="PASS", start=hit["start"], steps=hit["steps"], dispatcher=state,
                head=head, marker=head-1, header=hit["header"], distance=hit["header"]-head,
                empty_pc=True, physical_primaries=hit["values"][:9], logical_primaries=logical,
                spare_values=hit["values"][9:], one_cells=sorted(ones), one_count=len(ones),
                formula_T_certificate=classify(logical[1]), formula_H_certificate=classify(logical[5]),
                stack_certificate=stack_certificate(logical[2]),
                proof_scope="Exact finite blank trace and entire support; not an unbounded nonhalting test")


def canonical(table,start):
    states = {state for state,bit in table}
    order = [start] + sorted(states-{start})
    mapping = {old:new for new,old in enumerate(order)} | {254:len(order)}
    lines = ["#! start 0"]
    for old in order:
        for bit in (0,1):
            write,move,target = table[old,bit]
            lines.append(f"{mapping[old]} {bit} {write} {'L' if move<0 else 'R'} {mapping[target]}")
    return "\n".join(lines)+"\n", mapping


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("directory")
    args=ap.parse_args()
    root=Path(args.directory)
    summary=[]
    for path in sorted(root.glob("rotation*-blank-search.jsonl")):
        stem=path.name.removesuffix("-blank-search.jsonl")
        source=root/(stem+"-pruned.tm")
        table=read_table(source)
        results=[json.loads(line) for line in path.read_text().splitlines()]
        if {item["start"] for item in results} != {state for state,bit in table}:
            raise ValueError("Search omitted a retained start state")
        entry={"rotation":stem,"working_states":len(table)//2,"outcomes":dict(Counter(x["outcome"] for x in results)),
               "table_sha256":sha256(source.read_bytes()).hexdigest(),"verified_roots":[]}
        for hit in results:
            if hit["outcome"]!="SAFE_ROOT":
                continue
            proof=verify(table,hit)
            proof["old_table_sha256"]=entry["table_sha256"]
            output=root/(stem+f"-start{hit['start']}-bootstrap.json")
            output.write_text(json.dumps(proof,indent=2)+"\n")
            text,mapping=canonical(table,hit["start"])
            canonical_path=root/(stem+f"-start{hit['start']}-canonical.tm")
            canonical_path.write_text(text)
            canonical_path.with_suffix(".renumbering.json").write_text(json.dumps(mapping,indent=2)+"\n")
            entry["verified_roots"].append({"start":hit["start"],"steps":hit["steps"],
                "bootstrap_certificate":output.name,"canonical_table":canonical_path.name,
                "canonical_sha256":sha256(text.encode()).hexdigest()})
        summary.append(entry)
    (root/"blank-search-summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    print(json.dumps(summary,indent=2))


if __name__=="__main__":
    main()
