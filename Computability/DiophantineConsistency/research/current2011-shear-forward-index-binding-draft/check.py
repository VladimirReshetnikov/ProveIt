#!/usr/bin/env python3
"""Read-only source pins and interface markers; no Lean invocation."""
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
PINS={
 'research/current2011-shear-forward-index-binding-draft/ForwardIndex.lean.src':'fb39f3cb211700acd7e431da2f7a4e95a256a4a6f98087f8db0cb163beb9101a',
 'research/current2011-ordinary71-60-model-join/OrdinarySphere7160Model.lean':'98eda3763aa05598820c567e52a4c89d51a3aaaeed2912a925a9c1560d20ef98',
 'Lean/DiophantineConsistency/ArithmeticCarrier94Extraction.lean':'5e7ef8c7983af9a713b30a02616f00f81c3654b75574fecae944fee369c862f6',
 'Lean/DiophantineConsistency/ArithmeticCarrier94Indices.lean':'afc99ad41536f55e0f467581e4fbdbd5308036f93b6e3e10b1a5d2f1c113de4a',
 'Lean/DiophantineConsistency/ArithmeticPellFirstIndex.lean':'8cf79ed14f00f565accbfae0eb03ccacca597d06d12a509fecd6d3272e30f9ce',
 'Lean/DiophantineConsistency/ArithmeticCarrierRadix2011.lean':'87f89c10bd5499a4c7586d36138ded09fdcdb6968b16b954d30c1e335950c074',
 'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
}
for name,h in PINS.items():
 if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=h: raise RuntimeError('source pin changed: '+name)
MARKERS={
 'research/current2011-ordinary71-60-model-join/OrdinarySphere7160Model.lean':['theorem sameZero94','Carrier94Syntax.naturalExpression94'],
 'Lean/DiophantineConsistency/ArithmeticCarrier94Extraction.lean':['theorem current94_equations','ArithmeticCarrier94Soundness.OrdinaryEquations'],
 'Lean/DiophantineConsistency/ArithmeticCarrier94Indices.lean':['theorem ordinary_first_indices','2*R<k*Y+eta'],
 'Lean/DiophantineConsistency/ArithmeticPellFirstIndex.lean':['theorem scalar_window','0<q-F-alpha'],
 'Lean/DiophantineConsistency/ModelDifferenceRing.lean':['theorem ι_lt_ι'],
 'research/current2011-shear-forward-index-binding-draft/ForwardIndex.lean.src':['theorem natural_gap_and_half','theorem ring_half_of_casts','(hrank :','(hc :'],
}
for name,patterns in MARKERS.items():
 text=(ROOT/name).read_text()
 if any(x not in text for x in patterns): raise RuntimeError('interface marker missing: '+name)
print(json.dumps({'scope':'source hashes and interface markers only; draft not elaborated',
 'pinned_files':len(PINS),'interface_files':len(MARKERS),'rank_and_c_casts_explicit':True},indent=2,sort_keys=True))
