# Editable AX and theory/backend experiments

The frozen equality-free C/G compiler benchmark has **252 working
states**. The reviewed [finite-sort obstruction](typed_countermodel.md) rules
out the intended reduced abstract calculus as a consistency-search target;
the literal-table consequence remains conditional on its missing simulation.
The fixed-binder
PSC experiment costs 317 states; the unchanged public Wade backend reconstructs
the published program in 281 states. These measurements are not new verified
consistency-machine bounds.

Run offline from the repository root:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/theory_backend_experiment.py \
  --scratch /tmp/zfc-theory-backend \
  --output-evidence /tmp/theory-backend-results.json
```

Add `--search-orders` to reproduce the optional 288-case order/grouping search
recorded in `theory-backend-results.json`. The default uses the fixed best
recipe directly, without repeating that search.

The script reads the unchanged vendored snapshot at upstream commit
`297ab8df7e5de329605c3875b4934643b371a5e3`. It verifies hashes of the program,
the public MIT-0 backend, and the published `ZF/m254/tools/logic/spec.py`.
Generated machines and executed backend copies remain in the requested scratch
directory. The script does not need the unavailable `source.py`.

## Recovery before replacement

AX's published DAG expands to 186 macro calls. An independent symbolic stack
interpreter compares all resulting formula trees to the published specification:
GEN with the old cached formula; the eight logical rows; the CP/GIC/atomic
vacuity bundle; and the five original cleanup/freshness gate calls. The logical
prefix contains 88 calls. The read of the new cached parameter occurs after GEN.
The read of the fourth logical parameter restores the remaining proof list.

An editable re-emission shares only exact contiguous expansions of unchanged
published AX helper nodes. A minimum-token dynamic program finds the sharing;
re-expansion checks that it preserves every macro call and its order. Re-emitting
the original AX gives the same 219 decision states plus 62 framework states.
Its table hash differs because the AX root is renamed; all emitted decision
edges otherwise use the original source graph. This establishes a useful cost
baseline before replacing the theory formula.

## Equality-free candidates and the 252-state recipe

The raw variant retains GEN and the logical schemas rho8, rho6, rho4 and rho2.
It deletes the four equality schemas rho7, rho5, rho3 and rho1. The theory
bundle contains the published C and G formulas and membership vacuity only;
equality vacuity and the equality constructor disappear. The original
freshness checks `c≠a,b` and their cleanup remain. A control additionally emits
coextension-to-profile congruence, with a biconditional consequent:

```text
[∀c (c∈a ↔ c∈b)] → ∀c (a∈c ↔ b∈c).
```

The intended comparison theory for the raw variant is equality-free C/G with
irreflexivity. The machine does **not** emit an irreflexivity row: it uses
`Rel(0,0)` as its designated refutation target and as the falsity argument of
the derived constructors. A proof that this proof search is equiconsistent
with that comparison theory is outstanding. In particular, deleting equality
cannot inherit the original calibration by merely citing its Coq theorem.
The profile control also still requires the explicit theory-to-calculus bridge.

The fixed 252-state recipe is:

1. Keep GEN before the new cache read. Emit rho8, rho2, rho4, then the dual rho6.
2. Replace rho6 `(∃a ∀a b) → b` by `b → ∀a ∃a b`.
3. Emit the conjunction `V ∧ (C ∧ G)`, where V is membership vacuity.
4. Reuse exact published macro subsequences, then run the public backend's
   common-subsequence extraction **before** lowering to binary sequences.
   Independent re-expansion checks that macro order is preserved.
5. Use `Imp(A,B)=3P(A,B)`, `Rel(i,j)=3P(i,j)+1` and
   `All(i,A)=3P(i,A)+2`. Here `P(a,b)=tri(a+b)+b` is unchanged. Proof-list
   and theorem-stack pairing also remain unchanged. Only the formula scaler
   uses three increments per pair unit instead of four.

With ordinary classical falsity, dual rho6 is obtained schematically by
applying the old rho6 to `¬b`, contraposing, and removing double negations.
The runtime's `F=Rel(0,0)` is false uniformly only in the intended irreflexive
comparison semantics; quantifier label0 can otherwise capture that atom.
The substitution/quantifier congruence argument therefore still needs a Lean
proof in the precise relative-falsity calculus and its comparison bridge.
The script checks the Boolean identity `old(¬p) ↔ dual(p)`, with falsity fixed
false, in 98 nonempty finite Boolean matrices through domain size 4. This
does not prove the runtime schematic equivalence. It also executes 225 exact register
contracts for all three base-3 constructors, with small arguments and three
different residual theorem stacks. Every unused register is checked.

The optional search covers all 24 orders of the four logical rows, six orders
of C/G/V and two conjunction associations. The unique minimum among these
288 cases is the fixed 252-state recipe. This is a finite search in a selected
compiler family, not a lower bound. The unequal prefix experiment
`Imp=2P, Rel=4P+1, All=4P+3` cost 259 states in a scratch measurement and was
not selected. Base-3 tag permutations with nonzero Rel cost 254 or 255 before
the dual-rho6 change.

The generated named 252-state table is
`AX-raw_equality_free_C_G_shared_dual_base3.tm`, SHA-256
`06feea82f1ea6cbd7a93458d00e76c4afb14ab18e1cade3bb4afe1740dc48cab`.
It has 190 decision states, 62 framework states and 503 explicit rows. Its
sole undefined edge is handled by the separate standard-table normalization
and audit artifact. Its ZFC calibration, base-3 syntax interpretation,
enumeration soundness/completeness and compiler simulation are all open.

`Base3Encoding.lean` now proves one required freshness fact in Lean: for its
finite named membership/implication/universal syntax, every variable label,
including binder labels, is strictly below the base-3 formula code. Hence the
code itself is absent from all labels. Code positivity and the three remainder
tags are also proved, using only Lean's distribution and its arithmetic tactic.
The printed axiom dependencies are `propext` and `Quot.sound`. This theorem
does not cover the runtime's cyclic code0 truth alias or prove that every
natural is a decoded formula; it makes no codec-injectivity claim.

The frozen standard table is [raw-candidate-252.tm](raw-candidate-252.tm), with
504 rows, start0 and halttarget252; SHA-256
`58f8aab7fcc21a7e3a88e6250bf05b7a97eaafd340f75ea8117b6d8f989f3142`.
The [separate normalization/audit note](raw_candidate_252.md) records its
provenance, exact conventions, lack of conservative state reductions and
one-million-transition named/numeric lockstep check.

## New row and separate logical vacuity

Write `φ` for the matrix represented by parameter `c`, and use object-variable
labels 0 and 1 for its input and output. The new theory row is the conjunction
of fixed-variable extensionality and this subset-only point PSC:

```text
SB(φ) := ∀0 ∃c ∀1 [φ → ∀0 (0∈1 → 0∈c)]

SB(φ) → ∀1 ∃c [
    ∀0 [(0=1 ∨ 0∈c) → ∀1 (φ → 1∈c)]
  ∧ ∀1 [1∈c → ∃0 φ]
]

Ext := ∀0 ∀1 [(∀c (c∈0 ↔ c∈1)) → 0=1].
```

The root's label 1 appears in the guard before the inner output quantifier
shadows that label. The matrix always sees input 0 and output 1. The subset
test similarly binds label 0 only inside its consequent. The matrix must not
have free variable `c`. The intended numerical-code freshness argument, and
the treatment of excluded matrix codes 0 and 1, still require formal proofs.

The new theory row alone gets a local `c≥2` gate. The gate copies `c` to the
scratch registers, restores its source register, consumes two scratch units,
clears the theory top on failure, and clears the scratch remainder. The exact
register program passes 96 cases covering `c=0..23` and four current-top values;
all other register values are preserved. A false gate therefore leaves the
runtime's existing code-0 truth placeholder in that stack position.

After this gated row, AX emits a separate conjunction of the original atomic
membership/equality vacuity rows. The original `c≠a,b` gates and cleanup then
apply to that conjunction. **The new `c≥2` gate does not restrict these logical
rows.** Such a global restriction would lose full logical completeness: modal
two-world interpretations can make quantifiers 0 and 1 nontrivial and every
quantifier ≥2 the identity while satisfying the restricted schemas.

The new theory's 76 constructor calls and the vacuity row's 19 calls round-trip
through the independent symbolic interpreter. Derived conjunction, negation,
and existential quantification use the original constructors. All 66 cases of
nonempty domains of size 1 or 2, irreflexive membership relations, and arbitrary
binary matrix truth tables agree with a direct point-PSC/extensionality
semantics. Irreflexivity matters: runtime code 1 is `Rel(0,0)`, and derived
negation treats it as falsity. These are semantic regressions, not a theory
calibration proof.

## Measured result and remaining work

| Public backend variant | Decision | Framework | Working states |
| --- | ---: | ---: | ---: |
| Published DAG reconstruction | 219 | 62 | 281 |
| Editable original AX re-emission | 219 | 62 | 281 |
| Fixed-binder Ext/PSC, separate vacuity | 255 | 62 | 317 |
| Raw equality-free C/G | 197 | 62 | 259 |
| Equality-free C/G with profile control | 220 | 62 | 282 |
| Raw, reordered and shared | 193 | 62 | 255 |
| Raw, reordered/shared, base 3 | 192 | 62 | 254 |
| Raw, reordered/shared, base 3, dual rho6 | 190 | 62 | 252 |

Each table retains the public backend's one undefined `1.inc/read1` edge.
Undefined transitions use that backend's terminal convention; these outputs
are saved as named partial tables in scratch. A separate normalization artifact
records the total standard binary candidate. `PartialTotalization.lean` proves
the generic write-read-bit/right/halt rule preserves halting and final score,
with a precise attempted-step convention; parser, row correspondence and
compiler simulation remain outstanding.

The experiment preserves the published enumeration, logical rows, register
layout and arithmetic helpers. It changes the theory rows and their local
gating, so existing proof-search correctness cannot simply be inherited.
Required Lean work includes code-index freshness, alpha-renaming and matrix
coverage, the fixed-variable point-PSC calibration, the role of runtime falsity
and comparison irreflexivity, proof enumeration soundness/completeness, and
simulation of the changed compiler. No new ZFC equivalence or state bound is
claimed. A fresh compiler using the smaller Mira register engine is being
measured separately; it must charge a new initializer because the original
bootstrap depends on the original decoder.

