# Natural 82 to natural 86: ring/model source proposal

These are **uncompiled source drafts** for transporting the
[82-row natural graph](../ordinary14-natural-forced82-lean-draft/) to the
existing [86-row natural graph](../ordinary14-natural-cancel86-lean-draft/).
The files and their imports have not been elaborated, the proposed `simp`
and model conversion proofs may need repair, and their resource use is not
known. The source checker is not Lean and cannot establish the theorems.

The proposed ring identity is valid for arbitrary commutative-ring
valuations and signed integer ports, but **not at the same valuation**. Its
86-graph valuation is the 82-graph valuation minus one at slots `3`, `8`,
and `11` (the `f`, `r`, and `y` coordinates), and unchanged elsewhere. The
two small `k` and `r0` cut identities also account for the 86-to-85 zeta
rewrite. The checker compares the entire 86-to-82 DAG edit and runs finite
modular controls; those controls do not prove a universal ring identity.

`Natural82Model.lean` proposes a relation between two natural-model
valuations: the 82 values at the three slots are successors of the 86
values, and all other coordinates agree. Only under this relation does it
propose an `InternalZero` equivalence. A separate existence statement
**explicitly assumes** every 82 zero has predecessors at those three slots;
it does not prove this assumption. The reverse witness map increments the
three 86 coordinates, whereas the forward map needs those predecessors. The
external positivity argument for an 82 zero uses the unit-factor sign
exclusions, the negative-Pell argument, and the factors `F0`, `Fs`, `Fa`.
It requires separate formalization in the target model and suitable port
hypotheses; the ring identity alone cannot supply it.

The proposed model environment currently assumes `𝗜𝚺₁`, as in the existing
`ModelDifferenceRing` client. This is not a demonstration that the missing
predecessor assertion, the bridge, or any endpoint has an iPRA proof. No
coefficient-byte or PDF binding, provider coherence, or end-to-end
equivalence is established here.

The changed-valuation graph identity and the conditional model interface have
an [independent source review](../../reviews/ordinary14-natural-forced82-ring-bridge-independent/README.md).

```
python3 -I -S -B research/ordinary14-natural-forced82-ring-bridge-draft/check_source.py > /tmp/natural82-bridge.json
cmp /tmp/natural82-bridge.json research/ordinary14-natural-forced82-ring-bridge-draft/result.json
```
