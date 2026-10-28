# Actual C222 interpretation of internal source derivations: proposed leaf

26 October 2026. This is a **read-only implementation plan**, not a new Lean
theorem. No compiler, dependency build, or private overlay was started. The
proposed owned files are `ValidatorSourceDerivation222.lean` and
`ValidatorSourceDerivation222Checks.lean` under
`Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/`.

## 1. Exact source and target

Use the actual represented Foundation proof calculus over `ℒₛₑₜ`, with
`T : LO.FirstOrder.SetTheory` and `[T.Δ₁]`. Its internal predicates are
`Derivation T d`, `DerivationOf T d Γ`, `Proof T d p`, and `Provable T p`.
They are defined in Foundation's `FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean`
at lines 455–528. The ten cases are precisely `Derivation.case_iff`, lines
534–547, including the output `IsFormulaSet ℒₛₑₜ (fstIdx d)` condition.
There is no conversion to a standard-Nat proof tree.

Use the accepted C222 `ValidatorProvability222.CProv`,
`ValidatorFormulaEncoder222.encode`, `ValidatorProofContext222.seqC` and
`Enum`. In particular, `CProv g` means that an actual internally represented
`ArithmeticHistory222.value` equals `g+1`. No primitive `weq` equivalence or
semantic truth oracle is substituted for this predicate.

The only proposed imports are:

```lean
import ZFCinPA.ValidatorSourceNegation222
import ZFCinPA.ValidatorSourceQuantifierContext222
```

They already include Foundation's actual proof syntax. An explicit redundant
import of `Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic` would not
enlarge the closure. `R2Main.lean` was fully read as a historical guide; no
`ZFCinPA.R2*` module is in the proposed import closure.

## 2. Proposed exact interfaces and induction strength

Within `LeanProofs.ZFCinPA.ValidatorSourceDerivation222`, under
`[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`, define:

```lean
def AxOK (T : SetTheory) [T.Δ₁] (V : Type*)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Prop :=
  ∀ p : V, IsFormula ℒₛₑₜ p → p ∈ T.Δ₁Class →
    ∀ F s : V, StreamFree s F → CProv (encode F 0 s p)

def Inv (T : SetTheory) [T.Δ₁] (d : V) : Prop :=
  Derivation T d → ∀ F s L : V,
    StreamFree s F → Enum L (fstIdx d) → CProv (seqC F s L)
```

The principal theorem, now with the explicit additional instance
`[V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]`, is:

```lean
theorem translate (hAx : AxOK T V) : ∀ d : V, Inv T d

theorem cProv_falsum_of_provable (hAx : AxOK T V)
    (h : Provable T (^⊥ : V)) : CProv (1 : V)

theorem refutation_witness (hAx : AxOK T V)
    (h : Provable T (^⊥ : V)) :
    ∃ code : V, ArithmeticHistory222.value code = 2
```

These declarations deliberately retain `hAx`. They do not prove images of
Collection, Container, equality or any other actual source axiom. The `T`
parameter cannot silently become actual ZFC without supplying that missing
mathematical theorem.

Use `InductionOnHierarchy.order_induction_sigma 𝚷 2` on the internal code
`d`, not unrestricted metatheory induction on its value. The invariant is
Π₂: `Derivation` and `Enum` are Δ₁, `StreamFree` is Π₁, and `CProv` is Σ₁.
Promote `StreamFree` to Σ₂ and `CProv` to Π₂, use the accepted Σ₁ graph for
`seqC` promoted to Σ₂, then close under the three universal quantifiers and
implications. The exact `sigma1_to_pi2` and `pi1_to_sigma2` construction is
already used privately in `ValidatorEnvironmentAlpha222.lean`, lines 167–225.
Only the tiny local hierarchy instances must be restated; its internal
alpha-translation algorithm is not duplicated. This is not an IΣ₁ claim.

## 3. Small new helpers

`streamFree_tail` will prove `StreamFree s (tail F)` from `StreamFree s F`
under IΣ₁. Split `F` with `nil_or_adjoin`. The fallback-label inequality is
exactly `(h k).1`; avoidance of the tail follows from avoidance at index
`j+1` in the original cons. This needs no parity, distinctness, extra
freshness, bound-stack length or numerical lower bound on `s`.

`enum_cons` follows from `Enum.mem`/`enum_of_mem` and actual finite-set
insertion. `enum_shift` follows from `mem_shiftList`, `mem_setShift_iff`, and
the same membership equivalence. Duplicate list entries remain allowed.

A finite actual C222 propositional derivation will establish:

```lean
CProv (wim (wim (codeNeg b) (wim (codeNeg a) 1))
           (wim (codeNeg a) b))
```

This uses `double_neg_elim b`, `cProv_classical` and finite Kalmar deduction.
It is a theorem of the actual classical C222 validator, not an intuitionistic
HA double-negation rule. The final HA route still uses the separate accepted
negative-translation machinery.

## 4. Ten actual derivation cases

All branches first retain the actual output formula-set typing. Child-code
strict inequalities are the existing constructor lemmas in `Proof.Basic`,
lines 206–259; they apply to the internal ring model.

| Source case | Actual C222 construction |
| --- | --- |
| `axL` | The context contains negative encodings of `p` and source NNF `neg p`. From `encode_neg hp F 0 s`, use its backward implication and actual contraposition to recover double negation of the encoding of `p`, then close with its negative hypothesis. Source NNF negation is never identified definitionally with numeric negation. |
| `verumIntro` | `encode_verum` and actual `cProv_truth` contradict the encoded negative hypothesis. |
| `andIntro` | Apply the induction hypotheses to `p∷L` and `q∷L`, with actual `enum_cons`. Recover both positive encodings using `seqC_cons_iff_der`; combine with `ValidatorRelationalCore222.conj_rule` (or the equivalent accepted `conj_intro_imp`) and the typed `encode_and` identity. |
| `orIntro` | Apply the induction hypothesis to `p∷q∷L`. Two `der_ded` steps and the finite propositional helper above produce the actual encoded disjunction. Retain both source typing premises for `encode_or`. |
| `allIntro` | From source typing derive `IsSemiformula ℒₛₑₜ 1 p`. The child listing is `free p∷shiftList L`, with environment `eigen F s∷F` and the **same** stream `s`. Its safety is `fresh_resources F s hs .2.2.1`. Use `enum_cons` and `enum_shift`, then accepted `seqC_all`. Recover the positive ALL encoding via `seqC_cons_iff_der` and close against the parent's negative hypothesis. |
| `exsIntro` | Retain the actual arbitrary `IsTerm ℒₛₑₜ t`. The child listing is `substs1 t p∷L` at the unchanged environment and stream. Accepted `seqC_exs` gives the target sequent. There is no `term_is_fvar` reduction, parity condition, or freshness restriction on the term/context. |
| `wkRule` | Obtain an internal enumeration of the child sequent using `exists_enum`, apply its induction hypothesis, and use `der_sub` with actual `negEnc` membership and the source subset premise. |
| `shiftRule` | Enumerate the child and derive its typing from the actual child derivation. Apply its induction hypothesis at `tail F`, justified by `streamFree_tail`. The accepted `negEnc_shiftList` identity converts it to the shifted listing at `F`; actual source set-shift membership then gives `der_sub` into the parent listing. |
| `cutRule` | Apply the two child hypotheses at `p∷L` and source `neg p∷L`. Recover positive encodings, transport the second with `encode_neg hp F 0 s .1`, and apply actual numeric MP to get `1`. Typing of `p` comes from the first child formula-set condition. |
| `axm` | Invoke **only** the explicit `hAx` with the actual typed source code and `p∈T.Δ₁Class`; lift with `der_of` and close against context membership. This is the remaining theory-specific boundary. |

The ALL branch obtains all context vacuity from the accepted typed-source
quantifier theorem. It does not assume an unrestricted GEN-under-hypotheses
rule. `seqC_cons_iff_der` supplies the needed actual classical recovery, so
there is no new source-negation or semantic equivalence premise.

For the final falsum endpoint, unpack actual `Provable` into an internal
`Proof`, enumerate its singleton conclusion with `(^⊥ : V)∷0`, and use
`F=0`, `s=2`. `streamFree_of_bounds` proves this particular stream safety
from `0<2` and `1<2`. The exact sequent reduces to `(1→1)→1`; applying
`self_imp 1` gives actual `CProv 1`, hence a History222 value of `2`.

## 5. Minimal closure and frozen provenance

The companion [planning inventory](validator-source-derivation222-plan.json)
is SHA256 `9dc83e9ab42279fd86c004c171609a54c228703f922fafe458bba33f177f66ba`.
Its read-only script performed 760 hash observations followed by rehashing
every observation. Counts are exactly:

- 164 cached current-source modules, including 117 Foundation modules;
- 515 cached object/companion artifacts;
- 40 explicit package/toolchain boundaries, including implicit `Init` and
  the `public meta import Aesop` boundary;
- zero new Foundation modules, boundaries, dependency builds, Lean
  invocations or created overlays; only the proposed main/check pair would
  be freshly compiled after approval.

The delta from the accepted quantifier prerequisite inventory is exactly
the accepted `ValidatorSourceNegation222` and
`ValidatorSourceQuantifierContext222` main objects. Selected providers are
the independent Negation peer and the newly accepted Quantifier root replay.
Their original author provenance is preserved separately; no frozen metadata
was rewritten.

Quantifier root state is
`be351f9e011a5fc3ccedd5fd63a43b7c0094d8fe9b7cf57409da703d493a397d`;
its selected object is
`/tmp/validator-source-quantifier-context222-root-k2f0u7_b/lib/ZFCinPA/ValidatorSourceQuantifierContext222.olean`,
SHA `f187f3eb89782765795015866faece406faa9f2fbdeac5f19473a5b5c50e101c`.
Negation's accepted peer replay is
`f9013d100f8e3365c7fe19e39857ad9bba3fa5f3ef084c2a576d8745159294ef`;
its selected object is
`/tmp/validator-source-negation222-peer-ux05dhdf/lib/ZFCinPA/ValidatorSourceNegation222.olean`,
SHA `6155f06b7f9809a19ca7aec04c4f813fd69f58a41dc88e1a9a547f35eac6f119`.

Foundation `Proof.Basic` is already in the accepted 162-module quantifier
cache. Its current source is
`/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean`,
SHA `72e3cf386967e3fed4366ee5aa59678a0333cd2f40c8dbb09bebbf8dd4fa80e3`.
Its `.olean` is `c46f491eded2b033f450406537c1e02b6135a6b563f18a6cac1589f535ad5b69`.
The inventory retains all four object companions and the already authenticated
Lean4.32 Lake trace `46261510f78dd9bea0012eec997713da36ced1d8f31c06af21d163aef22d26ed`.
Current sources, all selected objects, boundaries and retained trace files
were rehashed. This is authenticated reuse, not a fresh Foundation replay.

## 6. Implementation and check boundary

One coherent main of roughly 250–320 lines and a focused check file should
suffice. If hierarchy elaboration requires a helper split, report that before
expanding ownership; no generic GG algorithm or source syntax is copied.
Checks should retain internal/duplicate enumeration, actual shift/tail
fallback behavior, singleton falsum, arbitrary-term EXS, the explicit
`AxOK` premise and actual value-2 witness. Report endpoint axioms, including
inherited standard metatheory axioms, without confusing them with validator
or HA proof rules.

After approval, use only two fresh regular output objects, private Lean4.32
`-M6000 -j1 -DElab.async=false`, one thread and the 512MiB reserve guard.
Preserve every failed draft/build and pre/post input observations. This plan
does not authorize old R2 semantic reuse, source axiom-image assumptions
disguised as theorems, execution/compiler overlap, or an HA equation claim.
