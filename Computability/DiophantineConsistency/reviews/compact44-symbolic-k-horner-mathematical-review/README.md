# Independent source review: compact symbolic K residue

Reviewed commit `50beffbc23`, including the successful
[`SymbolicKernelResidue.lean`](../../research/ordinary12-ipra-bridge/compact44-symbolic-k-residue-prototype/SymbolicKernelResidue.lean),
its compiler observation, the literal row and slot definitions, the selector
formula, and the conditional unit client's natural-cast interface. No defect
was found in the inspected mathematics. This is source inspection and an
external finite cross-check, not a second Lean replay or provider audit.

The reviewed theorem is exactly
`paramKernel rho % 342946332593 = 284898815895` in `ℕ`. The row coefficient
is formed in the naturals, including its truncated subtraction, before it is
cast to `ZMod`. The index bound `i<943` justifies the two natural-exponent
identities `4393-i=(942-i)+3451` and `5495-i=(942-i)+4553`. Thus factoring
the selector sum into the common row polynomial and two powers preserves the
row order and both reflected bands. The generic accumulator identity has the
right orientation for the ordered row list; the two finite residue checks use
`decide +kernel`. The final natural remainder is obtained from the `ZMod`
equality by `ZMod.val`, with the claimed residue below the modulus.

As a separate check, [`audit.py`](audit.py) parses the pinned ordered rows and
41 slots and computes the **unfactored** selector and copy sums modulo the
same modulus, rather than using the Horner accumulator. It obtains selector
residue `33533167632`, copy residue `299839741459`, bare-plus-temporal residue
`294472239397`, and total `284898815895`. It checks the row-value bound so its
ordinary subtraction agrees with natural truncated subtraction, checks the
relevant source/log hashes before and after, and rejects optimized Python.
This separate calculation manually transcribes the formula and is not a Lean
proof or validation of the source-to-object compiler chain.

The prior conditional unit theorem `gamma_unit_nat` would accept this natural
remainder as a premise and transfers it to a model with its `cast_mod_eq`
lemma. The two current author builds have different project providers; that
observation does **not** establish a combined model theorem or authenticate a
coherent provider. The successful residue compiler receipt pins the direct
symbolic-kernel object before and after, plus the source snapshot and output;
it inherits package, transitive, dynamic and between-check limitations. The
table and kernel source hashes inspected here are not a fresh proof that all
corresponding transitive objects were built from those bytes. Retained file,
gzip, displayed-equation, graph-zero and iPRA bindings remain outside this
review.
