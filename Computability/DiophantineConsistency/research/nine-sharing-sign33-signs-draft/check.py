#!/usr/bin/env python3
"""A source-presence check, explicitly not a Lean elaboration or proof."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent; D=P.parents[1]
source=P/'Sign33Draft.lean'; text=source.read_text()
assert 'UNCOMPILED RESEARCH DRAFT' in text and 'sorry' not in text and 'admit' not in text
names=['strong_norm_f_ge_two','windows_from_maintained_norms','gap_tau_signs','inner_V_signs','auxiliary_difference_sign']
for name in names: assert 'theorem '+name in text
upstream=D/'Lean/DiophantineConsistency/ArithmeticPellFirstIndex.lean'; u=upstream.read_text()
for name in ['scalar_window','maintained_first_indices']: assert 'theorem '+name in u
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print(json.dumps({'status':'PASS_PRESENCE_ONLY','draft_sha256':sha(source),'upstream_sha256':sha(upstream),'candidate_lemmas':names,'scope':'Source presence only; no Lean parsing, elaboration, kernel check, model transfer or endpoint.'},sort_keys=True,indent=2))
