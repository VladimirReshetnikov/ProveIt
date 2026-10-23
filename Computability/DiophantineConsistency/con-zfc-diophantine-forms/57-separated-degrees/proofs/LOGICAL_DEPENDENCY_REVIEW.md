# The consistency endpoint: exact scope of the inherited theorem

This package's new algebraic reductions preserve the existence of a
solution of the pinned parent systems. Their proofs are ordinary
mathematical arguments using integer arithmetic, finite sequences,
Pell equations, and the cited representation lemmas. They do not assume
that ZFC is consistent. The step identifying the pinned parent with
syntactic ZFC inconsistency is an inherited dependency, not a newly
verified theorem of this package.

## What the pinned source claims

At repository commit `4b4349064a750ba6347293b55874a7f92abdd0db`,
`Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md`
and `proof.md` explicitly state an ordinary mathematical proof,
formalizable in ZFC, of

```
Halt(K215, blank) iff there exists a finite ZFC refutation.
```

That ordinary proof composes a quantified source/runtime simulation,
the complete blank startup, the numerical command compiler, and an
inherited numerical-calculus-to-ZFC calibration. It is stated separately
from the external Lean and Rocq equivalences that were subsequently
checked. The command-calibration supplement gives the finite source
argument and explicitly names the numerical-calculus calibration as a
predecessor result. Thus the ordinary ZFC claim is not presented there
as an automatic consequence of trusting a theorem prover.

Byte-identical copies of these source statements, the calibration
supplement, the constructible-choice explanation, and the current
object-language status are in `../upstream/logical_calibration/`.
`SOURCE_PINS.json` records their repository paths and byte hashes.

## What this review establishes, and what it does not

This review inspected the source statements and the described proof
dependency chain. It did not independently reconstruct every preceding
numerical-calculus calibration, constructible-model theorem, or binary
runtime certificate. Consequently the appropriate formulation is:

> The new reductions are proved equivalent to the pinned parent
> predicates. Composing them with the inherited ordinary K215/compiler
> calibration gives the stated ZFC consistency equivalence. That
> inherited calibration remains a named proof dependency.

This is stronger than merely reporting finite test agreement, but it is
not a new end-to-end proof-assistant check of the consistency theorem.

## Why the object-language obligation remains separate

The repository's `OBJECT_ZFC.md` explicitly records that an external
Lean equivalence involving `BProv ZFCax_s [] Form.fBot` is not itself a
derivation in that calculus. The final two object-language sentences
and their `BProv` equivalence have not been assembled. The model's own
natural numbers may be nonstandard; agreement on external numerals or
truth in the standard natural numbers cannot discharge this obligation.

There is no logical contradiction in asking ZFC to prove the equivalence
between a fixed machine's halting and the existence of a ZFC refutation,
or between a fixed polynomial's unsolvability and Con(ZFC). Such an
equivalence does not prove either side unconditionally. In particular,
the constructible-model/completeness route to comparing ZF and ZFC
refutations is ordinary set-theoretic reasoning that can be developed
in ZFC. Its use does not require assuming Con(ZFC). Nevertheless an
external model-theoretic equivalence is not, without that internal
development or an explicit proof translation, an exported `BProv`
certificate. No such new certificate is supplied here.

The honest dependency distinction is therefore between an inherited
ordinary mathematical calibration and an unfinished literal
object-language formalization. The present review found no new logical
obstruction, but does not independently close the inherited calibration
or the repository's formalization gap.
