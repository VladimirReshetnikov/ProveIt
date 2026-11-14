#!/usr/bin/env python3
"""Replay exact graph comparisons against all 94 prior spanning tables.

This establishes table identity/difference and ordinary control quotient
counts. It does not establish historical consistency calibrations.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
from graph_tools import parse, canonical, sha

HERE=Path(__file__).resolve().parent
EXPECTED='7e1c6442816e5df05e961f2057719252a1976c9a195a786978bf1e2d3c8e466d'


def quotient(table,states):
    groups={q:0 for q in states}
    while True:
        bucket,new={},{}
        for q in sorted(states):
            key=tuple((w,d,groups[t]if t in states else -1)
                      for w,d,t in(table[q,0],table[q,1]))
            new[q]=bucket.setdefault(key,len(bucket))
        if len(set(new.values()))==len(set(groups.values())):
            return len(bucket)
        groups=new


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--candidate',type=Path,default=HERE.parent/'machine/machine.tm')
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    ledger=json.loads((HERE/'all_194_designs.json').read_text())
    packets=json.loads((HERE/'packet_ledger82.json').read_text())
    assert len(ledger)==94 and len(packets)==82
    candidate_hash=hashlib.sha256(args.candidate.read_bytes()).hexdigest()
    assert candidate_hash==EXPECTED
    candidate,states=parse(args.candidate)
    assert states==set(range(194)) and len(candidate)==388
    assert {t for w,d,t in candidate.values()}-states=={194}
    plain=canonical(candidate,states)
    broad=canonical(candidate,states,strong=True)
    assert plain is not None and broad is not None
    old_plain,old_broad=set(),set()
    matches,nontrivial=[],[]
    for item in ledger:
        path=HERE/item['table_file']
        assert hashlib.sha256(path.read_bytes()).hexdigest()==item['table_sha256']
        table,ss=parse(path)
        assert len(ss)==194 and len(table)==388
        a,b=canonical(table,ss),canonical(table,ss,strong=True)
        assert a is not None and b is not None
        assert sha(a)==item['canonical_class'] and sha(b)==item['strong_class']
        assert a not in old_plain
        old_plain.add(a);old_broad.add(b)
        if b==broad:matches.append(item['name'])
        q=quotient(table,ss)
        if q<194:nontrivial.append({'name':item['name'],'quotient':q})
    q=quotient(candidate,states)
    if q<194:nontrivial.append({'name':'PA194AX11G','quotient':q})
    assert len(old_plain)==len(old_broad)==94
    assert not matches and not nontrivial
    result={'status':'PASS','candidate_sha256':candidate_hash,
            'candidate_states':194,'candidate_transition_rows':388,
            'prior_spanning_classes':len(old_plain),'prior_strong_classes':len(old_broad),
            'candidate_plain_class':sha(plain),'candidate_strong_class':sha(broad),
            'exact_full_tuple_matches':matches,
            'transformations':['state renaming','every spanning start',
                               'global bit exchange','left-right reflection',
                               'ignored final halt write/move'],
            'ordinary_control_bisimulation_tables_checked':95,
            'nontrivial_control_quotients':nontrivial,
            'delivery_ledger_entries':len(packets),
            'historical_categories':dict(Counter(i['category']for i in ledger)),
            'scope':'Exact finite graph comparison. Symbol exchange is a strong structural novelty test, not a zero-blank semantic equivalence. No arithmetic calibration follows from graph comparison.'}
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
