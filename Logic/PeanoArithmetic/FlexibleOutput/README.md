# A divergent program with every possible output in a model of PA

**Status: proved in Lean.** The main theorem is
`PAFlexibleOutput.flexibleOutput` in
[`Lean/PAFlexibleOutput/Main.lean`](Lean/PAFlexibleOutput/Main.lean). Its
axioms are `propext`, `Classical.choice` and `Quot.sound`. The proof is four
modules, 255 lines in all.

## The theorem

There is a partial recursive function `f : ℕ ⇀ ℕ` such that for every `o`,
which is either a natural number `n` or `⊥`, the statement `f(0) = o` holds in
some model of first-order Peano arithmetic. The Lean theorem proves this for
every input, not only for `0`, and for a function that diverges everywhere:

```lean
theorem flexibleOutput :
    ∃ e : Code, (∀ x, Nat.Partrec.Code.eval e x = Part.none) ∧ ∀ (x : ℕ) (o : Option ℕ),
      ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔), ValueIn M e x o
```

The function is given by a program code `e`, and a model reads `f(x) = o`
through one fixed arithmetical formula `universalGraph(y, program, input)`,
"the program halts on the input with output `y`":

- `ValueIn M e x (some n)` says that the numeral `n` is the unique element `y`
  of `M` with `M ⊨ universalGraph(y, ⌜e⌝, x)`;
- `ValueIn M e x none` says that no element of `M` is such an output.

The same code and the same formula serve every `x` and every `o`. Three facts
make the formula a definition of `f` and not an arbitrary formula:

- `outputIn_nat`: in the standard model, `universalGraph(y, ⌜c⌝, x)` holds iff
  `y ∈ Nat.Partrec.Code.eval c x`; hence `valueIn_nat`: the value computed in
  `ℕ` is the real value;
- `universalGraph_uniq`: in every model of `𝗣𝗔⁻` the formula has at most one
  output for a given program and input, nonstandard programs and inputs
  included;
- `universalGraph_sigma_one`: the formula is `𝚺₁`.

Since `f` diverges on every standard input, `ℕ` is a model for `o = ⊥`, and by
`valueIn_nat` it is a model for no `o = n`: the models for the numerical
outputs are nonstandard.

The corollary `exists_partrec_flexibleOutput` in `Main.lean` is the statement
as worded above: a partial recursive `f : ℕ →. ℕ` with a program `e`, and for
every `o` a model of PA with `ValueIn M e 0 o`.

## Proof

Let `V_c(x, y)` be the *value sentence* "`y` is the only output of program `c`
on input `x`", an instance of the formula
`valueGraph(y, c, x) := ∀ z, universalGraph(z, c, x) ↔ z = y`. A structure
satisfies `V_c(x, n)` iff it computes the value `n`, that is, iff
`ValueIn M c x (some n)` (`models_not_valueGraph`, stated for the negation).

The values refuted by PA form a recursively enumerable relation: "PA proves
`¬V_c(x, y)`" (`provable_substs_re`). So a partial recursive `Search(c, x)`
returns some refuted value of `c` on `x` whenever there is one
(`exists_selector`). Kleene's second recursion theorem
(`Nat.Partrec.Code.fixed_point₂`) gives a program `e` with
`φ_e(x) = Search(e, x)`.

1. `e` diverges. An output `m` of `e` on `x` would be an output of the search,
   so PA would prove `¬V_e(x, m)`. But `m` would be the only real output of
   `e` on `x`, so `V_e(x, m)` would be true in `ℕ` (`valueIn_nat`), and `ℕ` is
   a model of PA.
2. PA refutes no value of `e`: a refuted value would make the search, and with
   it `e`, halt.
3. By the completeness theorem every value sentence `V_e(x, n)` holds in some
   model of PA, and that model computes the value `n`.
4. `ℕ` is a model in which `e` has no output.

The proof differs from the paper proof in the article at two points.

- The paper searches for a refutation of the halting sentence "`y` is an
  output", and obtains uniqueness of the output in step 3 from the
  functionality of the halting formula in models of PA. Here uniqueness is
  part of the sentence that is searched for, so step 3 needs no property of
  the model, and step 1 needs uniqueness in `ℕ` only, where it is the fact
  that a computation has one result. The functionality theorem
  (`universalGraph_uniq`) is still proved, in the module `Functionality`,
  which the main theorem does not use; with it, `V_c(x, n)` and the halting
  sentence for `n` are equivalent in every model of `𝗣𝗔⁻`
  (`valueIn_of_outputIn`).
- Step 1 uses that `ℕ` is a model of PA. The paper uses less, the consistency
  of PA alone: there PA verifies the finite computation (`𝚺₁`-completeness)
  and so proves both the halting sentence and its negation. The Lean proof
  takes the semantic route because it is shorter and Foundation provides
  `ℕ ⊧* 𝗣𝗔`; the first Lean proof (commit `410c820c4f`) followed the paper.
  The value sentence is not `𝚺₁`, so with it the paper's route is not
  available as it stands.

This is the self-reference proof (due to Vadim Kosoy) in Joel David Hamkins,
"Every function can be computable!", for one input at a time (the models for
different inputs may differ), and a consequence of Woodin's universal
algorithm; the article gives the references.

## Layout

| Path | Contents |
| --- | --- |
| [`Lean/PAFlexibleOutput/Halting.lean`](Lean/PAFlexibleOutput/Halting.lean) | `universalGraph`, Foundation's representing formula of the universal function of Mathlib's `Nat.Partrec.Code`; `OutputIn`, `ValueIn`; `outputIn_nat`, `valueIn_nat`; `valueGraph` and `models_not_valueGraph`; `universalGraph_sigma_one`. |
| [`Lean/PAFlexibleOutput/Provability.lean`](Lean/PAFlexibleOutput/Provability.lean) | `provable_substs_re`: for every formula `φ(y, c, x)`, "PA proves `φ` at the numerals `y`, `c`, `x`" is recursively enumerable, through the `𝚺₁`-definability of Foundation's arithmetized provability and numeral substitution. |
| [`Lean/PAFlexibleOutput/Search.lean`](Lean/PAFlexibleOutput/Search.lean) | `exists_selector`: a recursively enumerable relation has a partial recursive selector, by dovetailing. Mathlib only. |
| [`Lean/PAFlexibleOutput/Main.lean`](Lean/PAFlexibleOutput/Main.lean) | `flexibleOutput` and the corollary. |
| [`Lean/PAFlexibleOutput/Functionality.lean`](Lean/PAFlexibleOutput/Functionality.lean) | Not used by the main theorem. `code_uniq`: Foundation's representing formula of a partial recursive function has at most one output in every model of `𝗣𝗔⁻`, by induction on the code. `universalGraph_uniq`, `valueIn_of_outputIn`. 66 lines. |
| [`Lean/PAFlexibleOutput.lean`](Lean/PAFlexibleOutput.lean) | Import surface. |
| [`docs/Article/pa_flexible_output.tex`](docs/Article/pa_flexible_output.tex), [`.pdf`](docs/Article/pa_flexible_output.pdf) | The delivered draft: statement, mathematical proof, the Lean statement, the located repository and dependency results, and a five-stage route to a Lean proof. It predates the Lean proof and describes it as future work. |
| `docs/proposals/` | Arriving proposals for simplifying the Lean proof. A proposal is removed once it has been dealt with, so the directory is normally empty. |
| [`Research/delivery/`](Research/delivery/) | The rest of the delivered package, unchanged: `README.txt`, `verification_status.txt`, `dependencies.json` (pinned revisions and inspected sources), `notes/`, `scripts/`, `lean-toolchain`, and the three delivered Lean files in `lean/`. |

Notes on the Lean proof:

- Foundation's own `code_uniq` is commented out at the pinned revision, so the
  induction on the code in `Functionality` is new. The only case with content
  is minimisation, which needs the order of the model to be linear; this is
  why the statement is about `𝗣𝗔⁻` and not `𝗥₀`. In Lean one `simp` call
  unfolds the semantics of the formula in all cases and `grind` closes them,
  with trichotomy of the two candidate outputs as its only hint.
- In `Search` the semi-decision procedure of the relation is made to return
  its candidate before it is compiled to a code, so a bounded run of the code
  already yields the witness.
- In `Provability` the triple `((c, x), y)` is read as one number through
  Foundation's pairing, which agrees with Mathlib's `Nat.pair`
  (`nat_pair_eq`). The resulting predicate is `𝚺₁`-definable in `ℕ` because
  `Bootstrapping.Provable 𝗣𝗔`, formal numeral substitution and the
  projections are; Foundation's `re_iff_sigma1` turns that into `REPred`. The
  formula `φ` itself need not be `𝚺₁`. The code inside is the Gödel number of
  the instance of `φ`, and arithmetized provability of a Gödel number in `ℕ`
  is real provability (`provable_iff_provable`).

## The delivered scaffold

The package delivered three Lean files, now in
[`Research/delivery/lean/`](Research/delivery/lean/) with their delivered
bytes: `Statement.lean` (the concrete target and five named obligations, as
definitions of propositions), `ProofCore.lean` (the logical core over an
abstract interface) and `MathlibAssembly.lean` (the recursion-theorem argument
over an abstract arithmetic bridge and proof search). Their author had no Lean
executable and delivered them uncompiled, which their comments still say.

The first Lean proof, commit `410c820c4f`, compiled the three files unmodified
as modules of the library, discharged every obligation of `Statement.lean`
and proved its `MainClaim`, `StrongClaim` and `FullySpecifiedMainClaim` by
instantiating `MathlibAssembly`: eight modules, 1003 lines. The second
version, commit `7142f7f52b`, replaced that route by a direct argument with
the halting sentence: five modules, 376 lines. The current proof does not
import the delivered files, so they are no longer part of the library or of
any build.
They import only Mathlib and Foundation, and the delivered
`scripts/check_lean.sh` checks them from the `lean/` directory.

What the current proof does differently:

- the search takes the input as a parameter, so the theorem holds at every
  input and the clause "the search ignores its input" is gone;
- divergence comes from truth in `ℕ` and not from `𝚺₁`-completeness;
- the search is for a refutation of the value sentence and not of the halting
  sentence, so the functionality of the halting formula is not used;
- the abstract bridge, the search-implementation structure and the sentence
  for divergence are gone: `ValueIn` states both cases directly.

## Verification

Every module was elaborated in the root workspace (Lean `4.32.0`, mathlib
`v4.32.0`, the pinned Foundation submodule), one target per `lake` call, with
no errors and no warnings in the project's modules. Each of the seven
`#print axioms` lines reports `propext`, `Classical.choice`, `Quot.sound`.
There is no `sorry`, no added axiom and no `native_decide`.

The mathematical proof in the article has not been independently reviewed in
this repository.

## Building

The modules belong to the root workspace library `PAFlexibleOutput`. Build one
target at a time:

```powershell
$env:LAKE_JOBS = '1'; $env:LEAN_NUM_THREADS = '0'
lake build +PAFlexibleOutput.Main
```

Like `PAUndecidable`, the library imports Foundation and is therefore not part
of the `ProveIt.lean` facade.

## Provenance

Delivered as `docs/incoming/pa_flexible_output.zip` (arrival commit
`cb5ce85523`, 364,120 bytes) and placed on 2026-11-09. All thirteen entries of
the package's `SHA256SUMS` manifest matched the placed files; the manifest
itself is not filed, since the repository keeps no package-local checksum
ledgers, and remains in the archive at the arrival commit. The package's
`pa_flexible_output.{tex,pdf}` is under `docs/Article/` and everything else
is under `Research/delivery/`. The modules under `Lean/` were written in this
repository on 2026-11-09.
