#!/usr/bin/env python3
"""Replay the supplied compressed certificate without expanding its roots."""
import sys,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from whitehead_exposure.slp import grammar_graphs,verify_fused_exposure
from whitehead_exposure.selector import verify_exposure_graphs
from whitehead_exposure.engine import verify_presentation_trace
from whitehead_exposure.braid import verify_braid_certificate
p=json.loads((ROOT/'certificates/barrier_2pow1000.json').read_text())
G=grammar_graphs(p['grammar'])
assert verify_exposure_graphs(G,tuple(p['grammar']['alive']),p['exposure'])
assert verify_fused_exposure(p['grammar'],p['fused_move'],cap=100)
assert verify_presentation_trace(json.loads((ROOT/'certificates/barrier_m2.json').read_text()))
assert verify_braid_certificate(json.loads((ROOT/'certificates/native_braid_unknot.json').read_text()))
print('Three supplied positive certificates passed their respective replay checks.')
print('The compressed certificate has 1051 nodes and represents P_(2^1000).')
print('Only the native braid certificate includes topological input binding.')
