# Conditional arithmetic client for the 84/85 model maps

`ArithmeticComparison.lean` is **source-only and unelaborated**. Its three
bare imports and their transitive graph/provider dependencies are draft sources;
no Lean run, compiled object, arbitrary-model endpoint or external file
binding is claimed. Its two implications each include an actual source graph
zero and a positive valuation, as well as explicit additional arithmetic
premises. They are not an unconditional graph equivalence.

* `from84_with_carrier` derives the strict `w < gamma` needed by the reviewed
  conditional map from the separately proposed `gamma_gt_from_modified_balance`.
  The carrier scale, both Pell coordinates, first-index relation, natural
  balance, size/order bounds and identity `X=q*w` are explicit hypotheses.
* `from85_with_mersenne` derives `q ∣ X` via the separately proposed
  `mersenne_divides_X`, assuming an explicit Mersenne representation for `q`,
  `X=Exp.exp R`, and `q ∣ 3*X`. The factor-three cancellation is not valid for
  a general positive `q` without its stated radix premise.

The remaining key work is to extract the exact natural balance and index/Pell
identities from the 84 graph's own zero, and the corresponding power, residue,
and Mersenne representation from the 85 graph's own zero. Signed-to-natural
magnitude conversions, positivity and the compact beta cast must be proved in
the model; an ordinary-integer proof does not establish them. Review and
compilation of all dependencies, direct and transitive provider compatibility,
and an iPRA endpoint remain separate. Nothing here identifies physical bytes,
TeX or a PDF with the symbolic ports.

`python3 -I -S -B check_source.py` checks the stated source interfaces and
replays the three draft receipts. These are no-Lean source and finite controls,
not elaboration or a verification of the model implications. All tactics and
coercions remain subject to a future guarded Lean build.

Independent source review is recorded in
`../../reviews/ordinary14-84-85-arithmetic-client-draft-independent/`.
