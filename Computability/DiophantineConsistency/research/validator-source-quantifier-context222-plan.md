# Actual C222 quantifier rules through internal source contexts

Read-only implementation proposal by `circuit_reduction`, 26 October 2026.
This is step 3 of `c222-source-proof-interpretation-plan.md`. The context
packet is accepted at `f2a0118e28`; the source-negation packet remains separate.
No new Lean source, compilation, private overlay, or Git mutation was made
for this proposal. The companion inventory is
`validator-source-quantifier-context222-plan.json`, SHA256
`9dad1db62489fb5622829b826e26fccef1ace2315974200fe32878d7606b63f9`.

## 1. Proposed ownership and exact imports

Only these new files are proposed:

* `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSourceQuantifierContext222.lean`
* `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSourceQuantifierContext222Checks.lean`

The main imports only `ZFCinPA.ValidatorProofContext222` and
`ZFCinPA.ValidatorExistentialRules222`. The latter already imports the actual
QuantifierRules222, Streams222, Substitution222, Alpha222 and Vacuity222
resources. There is no need to import SourceNegation222, Foundation Proof.Basic,
or any R2 proof module for this leaf. The existing `R2Quant.lean` was read as
a historical guide only. Its parity-specific free-label construction and C254
provability conclusions are not reused as theorems.

All values below, including contexts, indices, source codes and environment
codes, range over `V` with `ORingStructure V` and IΣ₁. The complete source
quantifier interfaces additionally retain explicit IΣ₂, as required by the
already accepted uniform vacuity/alpha/substitution resources. `CProv` means
the actual `ValidatorProvability222.CProv` throughout; it contains an internal
`ArithmeticHistory222.value` witness. Internal vectors are not Lean lists.

## 2. Missing fold and its induction classification

Use the existing `imps`, `Der`, `negEnc`, `shiftList` and `seqC` definitions
without changing them. A useful general interface is:

```lean
-- Proposed, not yet implemented. Explicit IΣ₂.
cProv_gen_context (i g G : V)
    (hG : ∀ j < len G, Vac i G.[j]) :
  CProv (wim (wal i (imps G g)) (imps G (wal i g)))

der_gen (i : V) (hG : ∀ j < len G, Vac i G.[j])
    (h : Der G g) : Der G (wal i g)
```

The general induction predicate is
`(∀ j < len G, Vac i G.[j]) → CProv (wim (wal i (imps G g)) (imps G (wal i g)))`.
The bounded hypothesis is Σ₁, since `Vac i a` is the actual Σ₁ assertion
`CProv (wim a (wal i a))`; `len` and `nth` have fixed Δ₁ graphs. The
implication-to-Σ₁ predicate is safely represented as Π₂. Thus the generic
version uses explicit IΣ₂ order induction, `nil_or_adjoin`, and
`lt_adjoin'`. It must not be passed to the IΣ₁ vector induction tactic as an
arbitrary Lean predicate. Fixed graphs for `imps`, `wim`, `wal` and `CProv`
are reused; no new recursion is needed.

The nil case is self-implication. In the `a∷G` case, assume
`wal i (wim a (imps G g))` and `a`. The supplied `Vac i a` gives `wal i a`;
`all_distribution` gives `wal i (imps G g)`; the induction hypothesis gives
`imps G (wal i g)`. Two finite propositional deductions close the step.
`der_gen` then applies actual `cProv_gen` and this proved implication.

For the actual source contexts, the stronger induction classification is
available directly:

```lean
cProv_gen_source_context (F s g L : V)
    (hs : StreamFree s F)
    (hL : ∀ j < len L, IsFormula ℒₛₑₜ L.[j]) :
  CProv (wim
    (wal (eigen F s) (imps (negEnc F s L) g))
    (imps (negEnc F s L) (wal (eigen F s) g)))
```

With `F,s,g,hs` fixed, its induction predicate is a Δ₁ typed-list guard
implying a Σ₁ conclusion. This predicate is Σ₁, so the fold itself can use
`adjoin_ISigma1.sigma1_succ_induction`. The theorem still assumes IΣ₂ because
the step obtains vacuity from `encode_formula_vac`, whose own separate
formula-code induction needs IΣ₂. This distinction avoids advertising the
whole source generalization theorem as an IΣ₁ result. Implementing this
direct typed fold is preferred even if the generic Π₂ helper is also exposed.

## 3. Discharging every source-hypothesis vacuity

Propose a reusable `negEnc_vacuous` theorem with exactly `hs` and `hL` above:

```lean
∀ j < len (negEnc F s L),
  Vac (eigen F s) (negEnc F s L).[j]
```

Use `negEnc_len_nth` to select the actual typed source formula. In
`fresh_resources F s hs`, the first two components are precisely
`FreeAvoid (eigen F s) F` and `StreamAvoid (eigen F s) s`.
Then `encode_formula_vac` gives vacuity of its actual encoding at bound stack
0, and `ValidatorRelationalCore222.vac_neg` gives vacuity of the numeric
negative hypothesis. A membership-form corollary follows from `mem_negEnc`.

No blanket GEN-under-hypotheses axiom is introduced. No freshness of `g`,
length constraint on `F`, injectivity of labels, positive original stream,
or parity premise is added. The existing `StreamFree s F` premise retains
fallback label 1 and every future binder label. It may hold for stream 0
and repeated/zero stored labels; tests should preserve those cases rather
than replacing it by an unnecessarily restrictive bound on all parameters.

## 4. Exact ALL and EXS context endpoints

Under IΣ₂, with `hp : IsSemiformula ℒₛₑₜ 1 p`, propose:

```lean
all_intro_opened (F s L : V) (hs : StreamFree s F)
    (hL : ∀ j < len L, IsFormula ℒₛₑₜ L.[j])
    (h : Der (negEnc F s L)
      (encode (eigen F s ∷ F) 0 s (free ℒₛₑₜ p))) :
  Der (negEnc F s L) (encode F 0 s (^∀ p))

all_intro_shifted (F s L : V) (hs : StreamFree s F)
    (hL : ∀ j < len L, IsFormula ℒₛₑₜ L.[j])
    (h : Der (negEnc (eigen F s ∷ F) s (shiftList L))
      (encode (eigen F s ∷ F) 0 s (free ℒₛₑₜ p))) :
  Der (negEnc F s L) (encode F 0 s (^∀ p))

ex_intro_term (F s G : V) (ht : IsTerm ℒₛₑₜ t)
    (hs : StreamFree s F)
    (h : Der G (encode F 0 s (substs1 ℒₛₑₜ t p))) :
  Der G (encode F 0 s (^∃ p))
```

`all_intro_opened` composes the proved source-context GEN fold with
`all_opened_equiv hp F s hs`. For `all_intro_shifted`, first use the literal
`negEnc_shiftList` at free environment `eigen F s ∷ F`, with each typed source
formula's `isUFormula`, then `tail_cons`. The source `free` operation and
the environment cons remain explicit; there is no informal renaming step.

`ex_intro_term` is exactly `der_mp (der_of (ex_term_imp hp ht F s hs)) h`.
It needs no typing or vacuity premise on the arbitrary internal context `G`.
All freshness, alpha and equality-witness resources needed for the term
instance are already discharged by the actual `ex_term_imp` theorem.

Two short sequent wrappers are useful for the later interpreter, if they
fit the same leaf: actual `CProv (seqC (eigen F s∷F) s
(free p∷shiftList L))` implies `CProv (seqC F s ((^∀p)∷L))`, and actual
`CProv (seqC F s (substs1 t p∷L))` implies
`CProv (seqC F s ((^∃p)∷L))`. Use existing `der_byContra` to recover the
positive premise from the negated source hypothesis, apply the corresponding
context endpoint, then numeric double-negation introduction and
`der_undeduct`. These are finite C222 propositional deductions; they are not
a ten-case source-proof interpreter or an HA derivation.

Expose at least one explicit `ArithmeticHistory222.value code = conclusion+1`
witness corollary by unfolding `CProv`/`Der`. Do not substitute external
standard-Nat proof trees for these internally sized contexts.

## 5. Checks and implementation boundary

Estimate 220–300 main lines plus 60–90 focused check lines. Checks should cover
nil contexts, duplicate hypotheses, an arbitrary internal list length, the
exact shifted-environment identity, two source shifts, repeated labels,
stream 0 when its safety premise is available, and an arbitrary source term
using the fallback environment. Include explicit actual-history witnesses
for both quantifier directions used by the source rules. Print axioms for
the general fold, typed fold, vacuity discharge, opened/shifted ALL, EXS and
sequent clients. Imported standard `Classical.choice` is metatheory, while
the interpreted C222 propositional calculus itself is intentionally classical.

No new source formula recursion, alpha/substitution algorithm, semantic seed
theorem, primitive-equality-vacuity identification, proofword compiler,
source axiom image, complete source derivation interpretation, or HA endpoint
belongs here. In particular the tagged-seed/source-theory obligation remains
open after this packet.

## 6. Authenticated cache boundary

The proposed two imports have a source-header-closed union of **162 cached
modules, 117 Foundation modules, 513 object artifacts and 40 explicit package/
toolchain boundaries including Init**. There are no missing providers and no
new external boundary relative to the corrected encoder/context closure.
The ten-module increment over the 152-module encoder prerequisite inventory
is listed exactly in the companion JSON. It consists of the actual context,
atomic/indiscernibility transport, vacuity, alpha, stream, substitution,
quantifier and existential leaves, plus the existing syntax-only
`ValidatorEnvironmentSubstitution254`. No R2 module is in the import closure.

Select the independently accepted root objects for Context, Existential,
Quantifier, Streams, Substitution222, Vacuity, Alpha, EindContext and
AtomicTransport. Their source/object hashes are pinned with their root
receipts; all remaining pairs retain their accepted original provenance.
The current source, all selected object companions and explicit external
objects were rehashed before and after the read-only audit: 743 observations.
This authenticates reuse boundaries, not a fresh proof replay of Foundation
or every package. Only the proposed main and checks would be freshly built
after approval, with the established caps and disk guard.

The parser includes `public meta import Aesop`, preserving the historical
Context author inventory unchanged. Two planning-only preflight corrections
are retained: Foundation.IntProver repeats imports across public/meta modes,
and DominatedImplication explicitly imports Init in addition to implicit
Init. The new inventory deduplicates import names while retaining inherited
occurrences. Neither correction changes source, accepted metadata, compiler
output, or the closure boundary. The script and both failed preflight drafts
are pinned. No Lean process or overlay was created.
