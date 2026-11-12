# Independent source review: 75/74 literal graph drafts

The 75 and all-positive 74 source drafts match their independently reviewed
candidate JSON rows exactly and in order. Their fourteen witness slots and
four port slots match, all 75/74 nodes and all inputs/ports are live, and the
field structure projects the intended five factors and intermediate rows in
order. The displayed output shape matches the literal final product. The
review checker independently parses the actual Lean `let` lines rather than
trusting the author's generator, and reruns its `--check` receipt.

The exact row difference is deletion of `Fg=1+guard`, the guard-base change
from `g27−F` to `g27+qF`, and the product consumer change from Fg to guard.
With q=1+qm and 74's h equal to the old h+1, the guard factors agree by ring
algebra; 256 finite signed assignments are additional controls. These are
source and arithmetic checks, not a formal proof of the positive model map.
The distinct mixed-F-domain 74 graph is outside this review.

From `Computability/DiophantineConsistency` run
`python3 -I -S -B reviews/ordinary14-unit75-guard74-lean-independent/check.py | cmp - reviews/ordinary14-unit75-guard74-lean-independent/observation.json`.
The author source, checker, receipt and candidates are pinned. This review does
not establish Lean elaboration, factor-to-model binding, provider coherence,
model/halting/iPRA endpoint, exact degree, or physical-byte/PDF binding. No Lean
run was performed.
