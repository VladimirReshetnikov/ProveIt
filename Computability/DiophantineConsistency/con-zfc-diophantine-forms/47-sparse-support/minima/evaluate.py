#!/usr/bin/env python3
"""Evaluate either fixed polynomial modulo an integer, without huge expansions."""
import argparse
import json
import sys
from pathlib import Path
sys.dont_write_bytecode = True
from verify import evaluate_mod

ROOT = Path(__file__).resolve().parent
p = argparse.ArgumentParser(description=__doc__)
p.add_argument("circuit", choices=["75", "76"])
p.add_argument("modulus", type=int)
p.add_argument("witnesses", nargs=15, type=int,
               help="J F alpha z f h i T s w tau eta zeta e gamma, all positive")
a = p.parse_args()
d = json.loads((ROOT / ("gap_minima"+a.circuit+".json")).read_text())
print(evaluate_mod(d, a.witnesses, a.modulus))
