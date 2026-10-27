# Proposed finite actual C222 universal-rule checkpoint

Read-only audit and proposal by `controller_certificate`, 26 October 2026. No new Lean source, compilation, dependency build, cache copy or Git mutation was performed. Streams222 remains frozen. Proposed new leaf: `ValidatorQuantifierRules222.lean` and focused Checks, approximately 130–175 main lines and 45–60 checks. Approval is requested before implementation.

## Actual source rule and the old route

The source calculus is the represented Foundation Tait calculus. `Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic` defines `allIntro Γ p d = ⟪Γ,4,p,d⟫+1` and `exsIntro Γ p t d = ⟪Γ,5,p,t,d⟫+1`. Its `Derivation.case_iff` and actual constructor theorems require:

- ALL: `^∀p ∈ Γ`, with premise derivation of `insert (free set p) (setShift set Γ)`.
- EXS: `^∃p ∈ Γ`, `IsTerm set t`, with premise derivation of `insert (substs1 set t p) Γ`.

The typed wrappers `TDerivation.all'` and `exs'` retain those exact shifts and substitutions. A typed depth-zero formula may have free variables; it is not necessarily a closed sentence.

The complete old `R2Quant` and `R2Main` sources were read, including their actual ALL/EXS cases. Old R2Quant derives `all_step` and `ex_step` using odd free-label environments, an even binder stream and three fresh odd labels. Its source-proof induction translates a listed sequent into nested implications from **negated target encodings**, not by treating ALL as an unrestricted implication from one open formula to its universal closure. Old R2Main's uniform proof induction is Π2/IΣ2 and assumes separately established axiom encodability. Those semantic modules are source-only guides, not proposed imports.

The new Streams222 result permits a smaller first checkpoint: use the exact numeric opening identity plus formula-level relabelling, rather than transplanting old primitive-equality contexts or the two-binder chain.

## Existing literal constructor bindings

Write `E(F,B,s,p)` for actual `ValidatorFormulaEncoder222.encode F B s p`; `ex x P := neg (wal x (neg P))` and `neg P := wim P 1` are actual RelationalCore222 abbreviations. For internally typed `p` of bound depth1:

```text
E(F,0,x,^∀p) = wal x (E(x∷F,0,x+2,free set p))
E(F,0,x,^∃p) = ex x (E(x∷F,0,x+2,free set p))
```

These are frozen Substitution222 `encode_all_opened` and `encode_exs_opened`. They follow the literal binder equations, which push x onto the bound stack and advance the stream to x+2. Numeric `encode_free` first inserts x into the source free environment and then removes that free head via `encode_shift`; it does not shift x or alter the preserved bound stack. Typed nested binders are already covered by the accepted substitution induction.

For typed source formula A, `encode_shift` also gives:

```text
E(x∷F,0,s,shift set A) = E(F,0,s,A).
```

An EXS instance has the distinct exact identity:

```text
E(F,0,s,substs1 set t p) = E(F,z∷0,s,p),
z = TermLabels.term F 0 t.
```

When t is a free variable outside the stored environment, z is exactly fallback1. This identity alone is not an existential-introduction proof.

## Fresh resources and proposed endpoints

Work in an arbitrary internal IΣ1 model; the transport endpoints additionally require IΣ2. Let `hp : IsSemiformula set 1 p`, `hs : StreamFree s F`, and fix the explicit selector `x := alternateStart F s`. No old parity convention for F is imposed.

A finite resource lemma derives all of:

```text
FreeAvoid x F
StreamAvoid x s
StreamFree s (x∷F)
StreamFree (x+2) (x∷F)
StreamFree x F
```

Proof obligations are concrete: x exceeds F and1, so it avoids every stored label and fallback1; Apart s x gives `s+2*k != x` by choosing index0 in the x-stream; the original hs avoids F and1; every `x+2+2*k` is greater than x, F and1. The cons proof uses actual represented-list length/nth laws. Repeated and zero stored labels remain allowed. Original hs is retained and is not manufactured from the new selector. There is no assertion that s and s+2 are disjoint, nor a stream disjoint from both parity classes.

Define `P := E(x∷F,0,s,free set p)` and `Pnext := E(x∷F,0,x+2,free set p)`. `hp.free` is an actual depth-zero formula, so Streams222 relabelling with the two derived free-safety resources supplies actual CProv222 proofs `P→Pnext` and `Pnext→P`.

The first useful theorem is a genuine object-level binder equivalence, with no supplied proof of its desired conclusion:

```text
all_opened_equiv (hp) (F s) (hs) :
  let x := alternateStart F s
  CProv222 (wal x P → E(F,0,s,^∀p)) ∧
  CProv222 (E(F,0,s,^∀p) → wal x P)
```

Apply actual `all_mono x` to both body-relabelling proofs, rewrite the exact opened ALL at x, then compose with Streams222 relabelling of the typed source formula `^∀p` from stream x to s. An equally small `ex_opened_equiv` applies `ex_mono x` and the exact opened EXS identity, then relabels `^∃p`. This latter endpoint is an equivalence of quantified bodies; it is **not** the source EXS term rule.

The corresponding inference endpoints are:

```text
all_rule (hp) (F s) (hs) (h : CProv222 P) :
  CProv222 E(F,0,s,^∀p)

all_rule_under (hp) (F s H) (hs)
  (hH : Vac x H) (h : CProv222 (H → P)) :
  CProv222 (H → E(F,0,s,^∀p))
```

For the theorem rule, apply actual `cProv_gen x h` and the forward binder equivalence. For the hypothesis rule, `compose hH (all_mono x h)` proves `H→wal x P`, then postcompose the forward binder equivalence. Thus h is the prior rule-premise certificate, not a hidden proof of the desired universal result. The `Vac x H` guard is essential: the leaf must not assert the generally invalid unrestricted object theorem `P→∀x P` or generalize a derivation while silently carrying a nonvacuous assumption.

A concrete one-source-hypothesis client removes this vacuity premise by deriving it:

```text
all_rule_under_negated_source (hp) (hA : IsFormula set A) (F s) (hs)
  (h : CProv222
    (neg(E(x∷F,0,s,shift set A)) → E(x∷F,0,s,free set p))) :
  CProv222 (neg(E(F,0,s,A)) → E(F,0,s,^∀p))
```

Use exact `encode_shift`/`tail_cons`, actual `encode_formula_vac hA F s x` with the derived FreeAvoid/StreamAvoid resources, and `vac_neg`. This matches the real source ALL rule's shifted old hypothesis and opened principal formula. It is a finite one-hypothesis fragment, not yet a represented arbitrary sequent context. A positive encoded hypothesis variant is optional and immediate; an internal vector of arbitrarily many hypotheses should remain a separately reviewed context fold/induction checkpoint.

All conclusions can expose actual History222 numeric witnesses by unfolding the existing CProv222 predicate. There is no new induction in this leaf. Resource arithmetic uses IΣ1; IΣ2 appears exactly through accepted Alpha/Streams and, for derived hypothesis vacuity, Vacuity222.

## Equality boundary and deferred EXS/source-proof work

Source equality is encoded as Eind, not primitive `weq`. The proposed direct ALL/opened-EXS route does not need an equality-context substitution theorem: it uses accepted actual Alpha222 through Streams. It introduces no reverse Eind→weq implication and no primitive equality-vacuity oracle. If arbitrary H contains primitive equality, its Vac premise remains explicit; the source-hypothesis client is safe because the actual source encoder uses Eind and accepted Vacuity222 already handles auxiliary-label collisions.

A later real EXS term rule must derive `E(F,z∷0,s,p)→E(F,0,s,^∃p)` for the actual interpreted term label z, including z=1 from short free environments. That needs a singleton Eind-context transport and an actual equality witness (primitive weq→Eind in the permitted direction), with a fresh auxiliary binder and both required vacuity resources. Old R2Quant's primitive eqContext code cannot simply be renamed. This is a separate checkpoint after the finite ALL/opened-quantifier leaf. No semantic seed/calibration assumption is needed for the proposed leaf, but none is established either.

Arbitrary source-proof translation, sequent enumeration/negation folding, axiom encodability, CP/GIC and HA theoremhood remain open. Malformed source0 is not silently typed; the proposed rule endpoints require the stated typed p/A premises.

## Exact source and cache boundary

Proposed imports, in dependency order:

```text
ZFCinPA.ValidatorEnvironmentStreams222
ZFCinPA.ValidatorEnvironmentSubstitution222
```

The first contains actual Alpha222/Context222/Atomic222/RelationalCore222; the second adds only the already accepted syntax-only Substitution254 helper. Neither old R2Quant/R2Main nor old semantic CProv254 enters the new import closure.

The complete read-only plan is `research/c222-quantifier-rules222-cache-plan-20261026.json`, SHA256 `214674a0f44f8aec74f22ac6fc110862b9767572eaad994c36b487221aed3d1b`. Its topological closure is **159 cached sources / 117 Foundation modules / 510 artifacts / 40 external primary boundaries**; 715 hash observations and all actual import lists matched. No new Foundation module or prerequisite build is needed. No private overlay was created for this proposal.

Selected root providers are exact independently replayed objects:

- Streams222 source `098224c05370ebcf8e66210278efde2cd1199d15124daddf2ecdfc1863f33194`; root object `/tmp/validator-environment-streams222-root-peer-3wkkdg1f/lib/ZFCinPA/ValidatorEnvironmentStreams222.olean`, SHA256 `7761dd66700da8bc578bb73a9b7e8e58aa68b8317c85ee4e852edb996b560d89`; root record `8c92ebd1aaa4b4a960f1e74e349831d10351b38fe781b2d945a4db7bda32fbc1`.
- Substitution222 source `db2374e4030d1e6792e7426f59f0699796f9b85f78d66c53a478c488ef34ff61`; root object `/tmp/validator-environment-substitution222-root-peer-l0pz7nuu/lib/ZFCinPA/ValidatorEnvironmentSubstitution222.olean`, SHA256 `99f58288809049cc943f25f7d31b6755e8faec3aadca5732890896cf39a090fc`; root record `b025af75cdc63b67d75f0cefae28267ea809f554d3e30b72765dd06b2ea13af2`.

The plan pins source-only old guides separately, plus the current actual source-rule Foundation Basic/Typed and encoder contracts in its full prerequisite inventory. Their existing source/object provenance distinctions remain unchanged. Expected execution, only after approval: two fresh private leaves with `-M6000 -j1 -DElab.async=false`, complete pre/post pin checks, preserved attempts, and the 512 MiB disk reserve. This proposal authorizes no execution itself.
