#!/usr/bin/env python3
"""Verify the strengthened oracle and replay every admitted original site."""
from pathlib import Path
import sys,json,time
from collections import Counter
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import common
import source_invariant_affine as A

def controls():
    checked=0
    for r in range(9):
        assert A.oracle('95',None,('mark',r)) is None;checked+=1
        assert A.oracle('95',None,('mark',r),frozenset({r}))==('112',('plain',None),0);checked+=1
        for other in range(9):
            if other==r:continue
            assert A.oracle('95',(other,False),('mark',r),frozenset({r}))==('112',('plain',None),0);checked+=1
            assert A.oracle('95',(other,True),('mark',r),frozenset({other})) is None;checked+=1
        assert A.oracle('73',None,('mark',r),frozenset({r}))==('48',('plain',('inc',r)),0);checked+=1
        for effect in ('inc','dec'):
            for q in (*A.SKIP,'73','95'):
                assert A.oracle(q,None,('plain',(effect,r)),frozenset(range(9))) is None;checked+=1
    return checked

if __name__=='__main__':
    assert __debug__
    began=time.monotonic();n=0;minimum=10**9;rules=Counter();excluded=[]
    for pc,branch,target,halt in common.cases:
        if not A.case_allowed(pc,branch):excluded.append([pc,branch]);continue
        r,literal=A.run(common.T,pc,branch,target,halt=halt,fuel=1000)
        n+=1;minimum=min(minimum,literal);rules.update(r)
    assert n==8385 and len(excluded)==6
    result=dict(status='PASS',ordinary_mathematical_checker=True,new_Lean_endpoint=False,
                inductive_source_transfers=A.CHECKED_TRANSFERS,
                arbitrary_nine_register_root_transfers=A.ARBITRARY_ROOT_CHECKED_TRANSFERS,
                baseline_guard_cases=n,
                excluded=excluded,oracle_controls=controls(),minimum_literal_steps=minimum,
                rule_counts=dict(rules),seconds=time.monotonic()-began)
    (HERE.parent/'results/source-invariant-affine-verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
