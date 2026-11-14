#!/usr/bin/env python3
"""Retained-group heuristic. This script does not construct a TM."""
from pathlib import Path
import json
import source_language as s
import build221 as b
HERE=Path(__file__).resolve().parent
ops={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
def convert(t):
    if isinstance(t[0],str):return ops[t[0]],None if t[0]=='halt' else t[1]
    return convert(t[0]),convert(t[1])
def main():
    old=s.tree(json.loads((HERE/'baseline197.sites.json').read_text()))
    table=b.read_table((HERE/'baseline197.native.tm').read_bytes())
    groups,_=b.decoder_map(table,old)
    new=convert(json.loads((HERE.parent/'combined157.tree.json').read_text()))
    seen=set();queue=[new]
    while queue:
        t=queue.pop()
        if t in seen:continue
        seen.add(t)
        if not s.leaf(t):queue.extend(t)
    represented=set().union(*(ns&seen for ns in groups.values()))
    used=sum(bool(ns&seen)for ns in groups.values())
    added=sum(not s.leaf(t)for t in seen-represented)
    out={'baseline_working_states':len(table)//2,'baseline_reader_groups':len(groups),
         'new_internal_nodes':sum(not s.leaf(t)for t in seen),
         'engine_and_routing_convention':49,'retained_reader_groups':used,
         'unrepresented_new_nodes':added,'heuristic_total':49+used+added,
         'scope':'Retained-group estimate only; no allocated table or lower bound.'}
    if (len(table)//2,len(groups),used,added,out['heuristic_total'])!=(197,148,74,77,200):
        raise ValueError('recorded decomposition changed')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
