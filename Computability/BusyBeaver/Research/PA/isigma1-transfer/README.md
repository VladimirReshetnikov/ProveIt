# From IΣ₁ to iPRA for consistency machines

`ConPAISigma1Transfer.lean` proves a transfer theorem that does not depend on a machine.

Let `δ` be a bounded (`Σ₀`) formula of the language of arithmetic in one variable. Read
`∃ t, δ t` as "the machine halts, and `t` is a halting history". The file defines

```lean
def haltSentence (δ : ArithmeticSemisentence 1) : Sentenceᵢ language :=
  native (Semiformula.lMap embedding (∃⁰ δ))
```

the same sentence in the language of iPRA, read with intuitionistic connectives, and proves

```lean
theorem endpoint (δ : ArithmeticSemisentence 1) (hδ : Hierarchy 𝚺 0 δ)
    (h : 𝗜𝚺₁ ⊢ (paRefutation 🡘 ∃⁰ δ)) (hb : BoundCertificate) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence δ
```

Here `𝗜𝚺₁` is Foundation's theory, `paRefutation` is Foundation's provability predicate of
`𝗣𝗔` at `⊥` (`DiophantineConsistency.IPRAPA196Consistency`), and `standardTheory` is
standard iPRA. The axioms reported for `endpoint` are `propext`, `Classical.choice` and
`Quot.sound`.

`endpoint_sigma_one` is the same statement for an arbitrary `Σ₁` sentence `H` in place of
`∃ t, δ t`:

```lean
theorem endpoint_sigma_one (H : ArithmeticSentence) (hH : Hierarchy 𝚺 1 H)
    (h : 𝗜𝚺₁ ⊢ (paRefutation 🡘 H)) (hb : BoundCertificate) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence (bnd H)
```

The halting sentence is then the strict form `∃ w, bnd H w` of `H`, in which every
existential quantifier of `H` is bounded by `w`. In `𝗜𝚺₁` it is equivalent to `H`. So `H` may
be written with Foundation's `Σ₁`-definable functions.

## Models of PRA may be assumed to satisfy IΣ₁

`ConPAISigma1Models.lean` gives the same transfer in the form in which the endpoints of this
tree consume it: for sentences of the language of candidate PRA, so with its function symbols.

```lean
def ReductISigma1 (M : Type) [Nonempty M] [Structure language M] : Prop :=
  letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
  M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁

theorem halt_iff_refutation_of_models (halt : Semisentence language 1) (hopen : halt.Open)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        ((M↓[language] ⊧ ∃⁰ halt) ↔ (M↓[language] ⊧ mappedPARefutation)))
    (hb : BoundCertificate) :
    PRA ⊢ ((∃⁰ halt) 🡘 mappedPARefutation)
```

`forward_of_models` and `reverse_of_models` give `PRA ⊢ mappedPARefutation 🡒 ∃⁰ halt` and
`PRA ⊢ (∃⁰ halt) 🡒 mappedPARefutation` from the same hypothesis. These are the two hypotheses
of `PA194PRAAssembly.consistency_iff_nonhalting_of_classical_pra` and of its PA196 counterpart,
whose `haltClassical` is `∃⁰ haltMatrix` with an open `haltMatrix`.

So in a model argument for a machine reduction the model of candidate PRA may be assumed to
have an arithmetic reduct satisfying `𝗜𝚺₁`. `standard_isigma1` turns `ReductISigma1 M` into the
instance `M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁` for the arithmetic operations read off the PRA structure, which is
the assumption of `PA194RefutationBridge.mapped_refutation_iff`; `reduct_of_standard` is the
converse.

The general statements are `open_existential_of_models` (`∀ x̄ ∃ y θ` with `θ` open) and
`pi_one_iff_of_models` (`(∀ x p) ↔ (∀ x q)` with `p`, `q` open). They rest on
`finite_isigma1`: a sentence true in all these models follows in PRA from the image of one
theorem of `𝗜𝚺₁`, by completeness and the finiteness of proofs; the formalized conservation
theorems then remove that theorem.

## What this changes

For a machine `M`, the endpoints of this directory tree ask for two theorems of candidate
PRA, `PRA ⊢ mappedPARefutation 🡒 halt` and its converse. They have to hold in every model of
PRA, where only quantifier-free induction is available and where Foundation's proof
predicate has no theory.

By `endpoint`, one statement is enough instead:

    𝗜𝚺₁ ⊢ paRefutation 🡘 ∃ t, δ_M t

It can be proved by reasoning in an arbitrary model `V` of `𝗜𝚺₁`. There Foundation supplies
`Σ₁` induction, coded sequences and finite sets, functions defined by recursion, and the
internal syntax and proof theory of `𝗣𝗔` that its incompleteness development uses. The
machine still has to be verified inside `V`; a Lean theorem about runs over the ordinary
natural numbers does not transfer.

## What is not proved

- No machine equivalence. No formula `δ_M` is defined here and nothing is proved in `𝗜𝚺₁`
  about a machine.
- `hb : BoundCertificate` is a hypothesis. It is the proposition
  `PRA ⊢ lMap embedding (paRefutation 🡒 ∃⁰ bnd paRefutation)`, which is word for word
  `PA196ReverseGG.BoundCertificate`. `PA196PACertificateComplete.certificate` in
  `../pa196-vs-u208/ipra` proves it. It is left as a hypothesis so that this file imports no
  machine; I have not compiled that certificate on this machine.
- `haltSentence δ` is the mapped arithmetic sentence, not a sentence built from a function
  symbol for a halting test such as `PA194Bounded.haltSentence`. Relating the two for a
  particular machine is a separate statement of candidate PRA.

## How the proof goes

1. `classical_iff`: candidate PRA proves `mappedPARefutation 🡘 lMap embedding (∃⁰ δ)`.
   Both sides are put in the form `∀ x, open` by `PRABoundedPiOneUnary.unary_open`, using the
   certificate on the PA side, and the `𝗜𝚺₁` proof is transferred by
   `PRAISigmaOneOriginalEquivalence.comparison`, the formalized conservation of `𝗜𝚺₁` over
   candidate PRA for equivalences of such sentences.
2. `forward` and `reverse` carry the two implications into iPRA through the Gödel–Gentzen
   translation, in the way `PA194ForwardGG` and `PA196ReverseGG` do for an atomic halting
   matrix. Three lemmas of those files are restated here without their machine imports.

## Checking

The files import only modules of `DiophantineConsistency`. With those built in the root Lake
workspace:

```sh
bash Computability/BusyBeaver/Research/PA/isigma1-transfer/check.sh
```

`IPRA_LEAN_OVERLAY` and `IPRA_FOUNDATION_OVERLAY` are put in front of the search path when
set, as for `../pa194/ipra/check.sh`. The script compiles both files, prints the axioms of `classical_iff`,
`endpoint_sigma_one`, `endpoint`, `finite_isigma1`, `pi_one_iff_of_models` and
`halt_iff_refutation_of_models`, and fails if `sorryAx` occurs. It was run on Windows under Git Bash against the
root workspace (Lean 4.32.0); it was not run with overlays.
