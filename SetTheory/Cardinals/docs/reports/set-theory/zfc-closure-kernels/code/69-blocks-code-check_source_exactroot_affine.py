#!/usr/bin/env python3
"""Replay the exact-bootstrap variant against every admitted source case."""
from pathlib import Path
from collections import Counter
import json,time
import source_exactroot_affine as A
import check_source_invariant_affine as verifier

if __name__=='__main__':
    assert __debug__
    began=time.monotonic();n=0;minimum=10**9;rules=Counter();excluded=[]
    for pc,branch,target,halt in verifier.common.cases:
        if not A.case_allowed(pc,branch):excluded.append([pc,branch]);continue
        r,literal=A.run(verifier.common.T,pc,branch,target,halt=halt,fuel=1000)
        n+=1;minimum=min(minimum,literal);rules.update(r)
    assert n==8385 and len(excluded)==6
    # The common verification module's controls refer to its module binding;
    # selecting the exact-root module here has no process-external effects.
    verifier.A=A
    result=dict(status='PASS',ordinary_mathematical_checker=True,new_Lean_endpoint=False,
                initial_root=A.EXACT_BOOTSTRAP_ROOT,
                inductive_source_transfers=A.CHECKED_TRANSFERS,
                baseline_guard_cases=n,excluded=excluded,
                oracle_controls=verifier.controls(),minimum_literal_steps=minimum,
                rule_counts=dict(rules),seconds=time.monotonic()-began)
    output=Path(__file__).resolve().parent/'source-exactroot-affine-verification.json'
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
