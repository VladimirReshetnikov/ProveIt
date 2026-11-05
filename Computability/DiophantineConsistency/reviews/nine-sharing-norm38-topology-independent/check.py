#!/usr/bin/env python3
"""Read-only statement-presence check for an uncompiled generic draft."""
import hashlib,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];s=D/'research/nine-sharing-norm38-topology-draft/SharingTopology38.lean';h=hashlib.sha256(s.read_bytes()).hexdigest();assert h=='abcda964ca908f2c032d83c191a07fce8be4cd74c0c33294508f2a73a8ff16ff';t=s.read_text();assert 'Uncompiled' in t and 'sorry' not in t and 'admit' not in t
for x in ['g.left ∈ done ∧ g.right ∈ done ∧ g.target ∉ done','reference g.target = ringCompute g.op (reference g.left) (reference g.right)','ringRun gs env i = reference i','NormAssignment38.gatesHold embed ports w','fixedPoint_of_residuals']:assert x in t
print('PASS_STATEMENT_PRESENCE_ONLY: source SHA '+h+'; no Lean or graph-specific proof')
