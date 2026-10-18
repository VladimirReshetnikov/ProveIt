#!/usr/bin/env python3
"""Combine checked quiet source endpoints with the unused-workspace relation."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import workspace_affine as A
from source_exactroot_block_affine import endpoints
from source_block_affine import site_map
canon=A.canon
case_allowed=A.case_allowed

def run(table,pc,branch,target,halt=False,fuel=20000):
    assert halt==(site_map[pc][1]=='CH')
    if halt:return A.run(table,pc,branch,target,halt=True,fuel=fuel)
    ends=endpoints(pc,branch)
    assert ends and target==ends[0]['affine_target']
    pcs=frozenset(e['successor_normalized'] for e in ends)
    return A.run(table,pc,branch,target,halt=False,fuel=fuel,allowed_pcs=pcs)
