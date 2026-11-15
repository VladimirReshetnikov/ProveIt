#!/usr/bin/env python3
"""Finite bindings for the optional linear 2t halting-witness theorem.

This compares already certified aligned affine contracts. It neither reruns
the literal interpreter nor replaces its arithmetic soundness argument.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_DENSE = {
    "parent": "c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a",
    "candidate": "64ac4ba569b770688a39a1545d5536ad631d15dbb756a0584a8956a83943b3a8",
}


def read(p):
    return json.loads(p.read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def check(package, output):
    assert __debug__, 'Run verification without -O'
    old = package/'reference/AX11H'
    new = package/'machine'
    a = read(old/'independent/contracts.json')
    b = read(new/'independent/contracts.json')
    ia = read(old/'instructions.json')
    ib = read(new/'instructions.json')
    assert ia == ib and len(ia) == 3671
    assert len(a) == len(b) == 4778
    expected_index = [(i, positive) for i,row in enumerate(ia)
                      for positive in ([False,True] if row[0] == 'dec' else [False])]
    assert [(c['site'],c['positive']) for c in a] == expected_index
    assert [(c['site'],c['positive']) for c in b] == expected_index
    assert sha(old/'machine.tm') == EXPECTED_DENSE['parent']
    assert sha(new/'machine.tm') == EXPECTED_DENSE['candidate']
    assert ia[25][0] != 'halt'
    assert read(old/'sites.json')[25] == read(new/'sites.json')[25] == ['1000000','dec',8]
    halt_sites = [i for i, row in enumerate(ia) if row == ['halt']]
    assert len(halt_sites) == 1
    counts = Counter()
    changed = []
    for x,y in zip(a,b):
        assert (x['site'],x['positive']) == (y['site'],y['positive'])
        p,q = x['duration'],y['duration']
        assert len(p) == len(q) == 13
        assert all(type(v) is int and v >= 0 for v in p+q)
        assert p[0] >= 3 and q[0] >= 3
        assert p[1:] == q[1:]
        assert all(v <= 2*u and u <= 2*v for u,v in zip(p,q))
        assert all(108*v <= 119*u and 24*u <= 25*v for u,v in zip(p,q))
        if x['site'] in halt_sites:
            assert not x['positive'] and p == q == [3]+[0]*12
        delta = q[0]-p[0]
        counts[delta] += 1
        if delta:
            changed.append({'site':x['site'],'positive':x['positive'],
                            'parent_constant':p[0],'child_constant':q[0],
                            'difference':delta})
    startups = []
    for folder in (old,new):
        receipt = read(folder/'independent/receipt.json')
        assert receipt['status'] == 'PASS'
        assert receipt['contracts_sha256'] == sha(folder/'independent/contracts.json')
        assert receipt['native_sha256'] == sha(folder/'machine.native.tm')
        assert receipt['dense_sha256'] == sha(folder/'machine.tm')
        startups.append(receipt['startup_steps'])
    assert startups == [57922,57922]
    assert startups[0] >= 4
    result = {'status':'PASS',
      'scope':'Finite aligned-duration inequalities for the separately written linear 2t theorem',
      'contracts':len(a),'source_sites':len(ia),'halt_sites':halt_sites,
      'common_startup':startups[0],'stopped_duration':'D_j(H)=0',
      'exact_complete_contract_index':True,'exact_literal_machine_hashes':True,
      'all_variable_coefficients_identical':True,
      'constant_difference_counts':dict(sorted(counts.items())),
      'changed_contracts':len(changed),'changes':changed,
      'parent_to_child_duration_inequality':'D_child <= 2*D_parent',
      'child_to_parent_duration_inequality':'D_parent <= 2*D_child',
      'stronger_checked_inequalities':['108*D_child <= 119*D_parent','24*D_parent <= 25*D_child'],
      'halt_instruction_duration':3,'source_halt_witness_bound':'t+1',
      'linear_witness_map_both_directions':'2*t',
      'hashes':{str(p.relative_to(package)):sha(p) for folder in (old,new)
          for p in (folder/'independent/contracts.json',folder/'independent/receipt.json',
                    folder/'instructions.json',folder/'sites.json',folder/'machine.tm',folder/'machine.native.tm')}}
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','contracts','changed_contracts',
                     'constant_difference_counts','linear_witness_map_both_directions')},indent=2))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package',type=Path,default=ROOT)
    p.add_argument('--output',type=Path,default=ROOT/'verification/linear_clock_audit.json')
    a = p.parse_args()
    check(a.package,a.output)
