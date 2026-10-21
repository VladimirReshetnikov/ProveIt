#!/usr/bin/env python3
"""Portable pinned source/decoder support for the encoding experiments."""
import os, sys, json
from pathlib import Path
from functools import cache

W = Path(os.environ.get('ENCODING_WORKSPACE', Path(__file__).resolve().parent)).resolve()
os.environ['K221_BASE'] = str(W/'K221_Construction_2026-10-20')
os.environ['ENCODING_OUTPUT'] = str(W/'generated_support')
sys.path.insert(0, str(W/'K220_Construction_2026-10-20/research/encoding/scripts/rows'))
import search as z
s,b=z.s,z.b

@cache
def flat(n):
    return (n,) if s.leaf(n) else flat(n[0])+flat(n[1])


def at_interval(t, lo, hi):
    hits=[]
    def go(n, start=0, p=''):
        stop=start+len(flat(n))
        if start==lo and stop==hi: hits.append(p)
        if not s.leaf(n):
            go(n[0],start,p+'0');go(n[1],start+len(flat(n[0])),p+'1')
    go(t)
    assert len(hits)==1,(lo,hi,hits)
    return hits[0]

