# Eleven unrestricted integers: exact one-gate savings

New degree/gate pairs: **298/146** and **300/144**, improving the frozen
Round20 pairs298/147 and300/145 by one live binary gate each.
The first polynomial is identical; the second is an explicit integral
n-shear. The complete formulas, ordinary proof, safe late-scale handoff,
actual-degree certificates and theorem boundaries are in `PROOF.md`.
The eleven-integer domain and complete six-number tuple are unchanged.
This component is separate from the ten-positive/four-number family.

The restricted degree floors remain298 in the rebased frame and300 in the
old frame. No global or operation-count optimum, consistency proof, or new
end-to-end proof-assistant certificate is claimed.

```sh
python -B build.py --check
python -B check.py --receipt CHECK.json
python -B -O check.py --receipt CHECK_OPTIMIZED.json
python -B audit_mutations.py
python -B -O audit_mutations.py
python -B replay.py
```

`check.py` independently authenticates every arithmetic gate, all complete
center remainders and highest coefficients, and reconstructs the six actual
numerals. A separate checker binds23 full top forms. The mutation audit
rejects580 altered operation labels. Root manifests are the active release
indexes; nested manifests are historical provenance, as explained in
`CLOSURE_MAP.md`. All required proof texts and coefficient payloads remain.
