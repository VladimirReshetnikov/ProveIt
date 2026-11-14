#!/usr/bin/env python3
"""Replay the bounded PA194H6 contraction screen; use normal Python, not -O."""
import json,sys
from pathlib import Path
import verify_reductions as v
if not __debug__:raise SystemExit('Assertions are certificate checks; do not use Python -O.')
if __name__=='__main__':
    print(json.dumps(v.whole_contract_merges('PA194H6'),indent=2))
