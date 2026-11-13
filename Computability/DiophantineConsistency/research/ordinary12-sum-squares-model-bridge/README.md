# 94-operation model and byte-recipe halt bridge

`SumSquaresModelIff.lean` joins the checked same-valuation replacement in
[`ordinary12-sum-of-squares-candidate`](../ordinary12-sum-of-squares-candidate/)
to the existing 95-operation model halt and byte-port theorems. It proves,
for every model `V` of `IΣ₁`:

* `positive_model_iff`: a strictly positive valuation makes the symbolic-port
  94-expression zero exactly when the represented machine has a model halt;
* `shifted_model_iff`: after substituting `x + 1` for each witness, an
  arbitrary valuation makes the symbolic-port expression zero exactly when
  the represented machine has a model halt;
* `shifted_byte_model_iff`: the same shifted statement with all four ports
  decoded from the exact closed Lean byte-recipe lists.

Here “model halt” means precisely the displayed Lean proposition
`∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0`.
A nonstandard model's witness may be nonstandard. The shifted expression has
12 natural-valued witness coordinates; the unshifted expression and the
external graph are presented over strictly positive coordinates. The
coordinate shift changes the displayed expression and should be counted
separately if those additions are included in an operation count.

The bridge uses the unchanged `FreeJSumSquares.zero_iff_literal` theorem at
each valuation and the existing unconditional 95-expression model theorem.
For the shifted recipe statement, `internalZero_positiveShift` connects the
same shifted valuation to each unshifted expression, and the existing
`CompactBytePortsModelIff.shifted_model_iff` supplies the halt equivalence.
The byte decoder is the natural `Nat.ofDigits 256` from the earlier checked
four-port assembly, followed by a cast to the integer port type.

## Check and provenance

`observations/attempt01/` records the bounded Lean check. It exited 0 with no
warnings or `sorryAx`; each theorem reports the Lean axioms `[propext,
Classical.choice, Quot.sound]`. The checked source SHA-256 is
`256b9f9d5202b3d1d7d10116467c5b1aa4351e0eb125d0ffc8fd918911ec67c5`, and
the new compiled object SHA-256 is
`881d0dab814d2bad6ba16cf703d0ed3f717ac2792f5819abd65f4b19b11fd583`.

`run.py` verifies the existing selected byte/model manifest (1,286 files),
producer and guard receipts, both immediate producer objects, and all 167
files from the 94 theorem's recorded provider inventories against shared
selected names and hashes. It constructs an isolated 1,288-file selected
union by adding the 94 theorem and the byte-model theorem objects, records
direct dependency/companion guards, and checks the inputs and union again
after compilation. The command, selected files and guard records are in the
terminal receipt. Provider validation checks recorded and live artifacts;
it does not reconstruct every historical source-to-object compilation. The
runner can be repeated with a fresh `ATTEMPT` environment value if its
recorded temporary providers remain available.

The all-model theorem concerns Lean expressions and Lean byte lists. It is
not an iPRA derivation of the equivalence and does not prove that external
JSON, gzip payloads, a PDF, or any other filesystem bytes equal the Lean
expressions or lists. The candidate's separate external graph comparison and
degree-84 evidence do not remove those formal boundaries. In particular, this
packet does not finish the end-to-end iPRA consistency-equivalence goal.
