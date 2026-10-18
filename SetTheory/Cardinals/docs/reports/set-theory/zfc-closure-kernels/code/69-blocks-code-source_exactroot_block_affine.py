#!/usr/bin/env python3
"""Quiet-block checker requiring the exact context246 source bootstrap root."""
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
if str(HERE) not in sys.path:sys.path.insert(0,str(HERE))
import source_exactroot_affine as A
from source_block_affine import BlockChecker,oracle,canon,canon_side,SKIP,PHYSICAL

DEFAULT=BlockChecker(A)
run=DEFAULT.run
endpoints=DEFAULT.endpoints
case_allowed=DEFAULT.case_allowed
zero_registers=DEFAULT.zero_registers
CHECKED_TRANSFERS=A.CHECKED_TRANSFERS
EXACT_BOOTSTRAP_ROOT=A.EXACT_BOOTSTRAP_ROOT
