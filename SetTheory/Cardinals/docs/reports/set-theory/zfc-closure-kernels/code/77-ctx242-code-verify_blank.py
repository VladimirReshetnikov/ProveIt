#!/usr/bin/env python3
"""Check exact table renumbering and the finite blank startup in two simulators."""
from pathlib import Path
from hashlib import sha256
import json
import argparse
from verify_induction import parse

ROOT=Path(__file__).resolve().parents[1]
STEPS=407979
CANON_SHA='ef8c07f372c76a73c021f51801f16f28f1e4ca5ead2d4ce6780c2a245a0db245'
OLD_SHA='c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02'

def sparse(table,start,n):
    q,h,ones=start,0,set()
    for _ in range(n):
        w,d,q=table[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    return q,h,sorted(ones)

def dense(table,start,n):
    offset=n+1
    tape=bytearray(2*n+3)
    q,p=start,offset
    size=max(q for q,b in table)+1
    rows=[None]*(2*size)
    for (q0,b),row in table.items():rows[2*q0+b]=row
    for _ in range(n):
        w,d,q=rows[2*q+tape[p]]
        tape[p]=w
        p+=d
    return q,p-offset,[i-offset for i,b in enumerate(tape) if b]

def target_ones():
    ones={-6,176}
    cursor=177
    for value in [0,0,0,3,0,0,3,0,0]+[1]*167:
        ones.update(range(cursor+1,cursor+value+2))
        cursor+=value+2
    return sorted(ones)

def main():
    if not __debug__:raise RuntimeError('Assertions must be enabled.')
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=ROOT/'evidence/blank-audit.json')
    args=ap.parse_args()
    inherited_path=ROOT/'machine/zfc_return_fold242_old.tm'
    canonical_path=ROOT/'machine/zfc_return_fold242.tm'
    assert sha256(inherited_path.read_bytes()).hexdigest()==OLD_SHA
    assert sha256(canonical_path.read_bytes()).hexdigest()==CANON_SHA
    inherited=parse(inherited_path)
    labels=[95]+sorted({q for q,b in inherited}-{95})
    renumber={q:i for i,q in enumerate(labels)}
    renumber[254]=242
    canonical={(renumber[q],b):(w,d,renumber[t]) for (q,b),(w,d,t) in inherited.items()}
    data='#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n'
        for (q,b),(w,d,t) in sorted(canonical.items()))
    assert data.encode('ascii')==canonical_path.read_bytes()
    supplied=json.loads((ROOT/'machine/renumbering.json').read_text())
    assert {int(q):n for q,n in supplied['old_to_new'].items()}==renumber
    assert {int(n):q for n,q in supplied['new_to_old'].items()}=={n:q for q,n in renumber.items()}
    expected=(96,-5,target_ones())
    expected_canonical=(86,-5,target_ones())
    assert renumber[96]==86
    assert sparse(inherited,95,STEPS)==expected
    assert dense(inherited,95,STEPS)==expected
    assert sparse(canonical,0,STEPS)==expected_canonical
    assert dense(canonical,0,STEPS)==expected_canonical
    report={'status':'PASS_EXACT_BLANK_PREFIX_AND_RENUMBERING','working_states':242,
        'binary_rows':484,'start':0,'halt':242,'dispatcher':86,'old_start':95,
        'old_halt':254,'old_dispatcher':96,'steps':STEPS,
        'canonical_sha256':CANON_SHA,'inherited_sha256':OLD_SHA,
        'head':-5,'marker':-6,'header':176,'span':181,
        'physical_registers':[0,0,0,3,0,0,3,0,0],
        'logical_registers':[3,0,0,0,3,0,0,0,0],
        'spare_values':[1]*167,'all_one_positions':target_ones(),'one_count':351,
        'all_other_cells_zero':True,'sparse_dense_and_both_numberings_agree':True,
        'scope':'Exact finite initialization and canonical renumbering; universal proof is separate.'}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('all_one_positions','spare_values')},indent=2))

if __name__=='__main__':main()
