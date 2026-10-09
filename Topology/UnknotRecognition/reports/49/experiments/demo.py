#!/usr/bin/env python3
"""Produce an explicit algebraic source and replayable research certificate."""
from pathlib import Path
import json
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'src'))
from anchored_unknot import AnchoredState, replay
from anchored_unknot.fixtures import power_chain
root = Path(__file__).resolve().parents[1]
source = power_chain(6, 8)
state = AnchoredState(source)
proof = state.run(max_pairs=1)
verified = replay(source, proof)
assert verified.rank_one_zero and not verified.needs_torsion_freeness
(root/'data/demo_source.json').write_text(json.dumps(source.payload(),indent=2)+'\n')
(root/'data/demo_certificate.json').write_text(json.dumps(proof,indent=2)+'\n')
print('Algebraic rank-one endpoint verified; not a knot-diagram verdict.')
print('Cumulative images:',verified.images)
