# Lean formalization of the synthesis

Lean 4 (v4.32.0) + Mathlib (v4.32.0) formalization of
`docs/research-synthesis/Large_Cardinals_Synthesis.tex`.  Set theory is done inside
Mathlib's model `ZFSet` of ZFC; first-order syntax, the ZF axioms and the Choice formula
come from the sibling repository `C:\ProveIt` (libraries `FirstOrder`, `ZF`,
`BoundedZFCConsistency`), which is required by path in `lakefile.toml`.

## Build

```sh
# once: share ProveIt's package cache instead of re-downloading/rebuilding Mathlib
powershell -Command "New-Item -ItemType Junction -Path .lake\packages -Target C:\ProveIt\.lake\packages"
lake build
lake env lean Cardinals/Audit.lean     # prints the axioms behind each main theorem
```

## Policy on admitted statements

Only results from the literature are admitted, each closed by the tactic `admit` with its
source in the docstring; nothing else uses `sorry`.  Five statements that were admitted in
earlier versions are now **proved** from the definition of a witness (they keep their names
in `Published.lean` so that nothing downstream changed): `cof_omega_of_witness`,
`aleph0_lt_of_witness`, `strongLimit_of_witness`, `not_REx_shortCofinal` (Blue–Goldberg
Observation 1(2)) and `le_of_CEx`.  Their only admitted ingredient is `critSeq_cofinal`
(the Kunen inconsistency).  16 admitted statements remain:

| File | Admitted statement | Reference |
|---|---|---|
| `Published.lean` | `REx_transfer` | BG, Lemma 3.3 |
| | `stationary_of_CEx` | BG, Proposition 3.4 (1)⇒(3) |
| | `isClub_elemSub` | Jech Ch. 8 (clubs in P_κ(A)) and Ch. 12; Kanamori §25 |
| | `ODfrom_trans` | Jech Ch. 13 (ordinal-definable sets), Thm 12.14 (reflection) |
| | `SC_of_extendible` | Kanamori Prop. 23.6, §22; Jech Ch. 20 |
| | `HCD_isInnerModelZF`, `HCD_isInnerModelZFC`, `HCD_cover`, `HCD_stabilizes` | Goldberg, arXiv:2103.13961v2, Prop. 4.2, Thm 4.3, Thm 4.13, Thm 4.14 |
| `Above.lean` | `HCD_isGround` | Goldberg, arXiv:2103.13961v2, Thm 4.9 |
| | `cc_preserves_regular` | Kunen 1980, Ch. VII Lemma 6.9; Jech Ch. 15 |
| `Virtual/Constructible.lean` | `lExacting_absolute` | Jech Thm 25.20 (Shoenfield absoluteness), applied to the `Σ¹₂` statement "some countable ordinal is L-exacting" |
| `Virtual/Restriction.lean` | `exists_vonNeumann_formula` | Jech Ch. 6 and Ch. 12 (the cumulative hierarchy is definable and absolute for transitive models of ZF); Kunen 1980, Ch. IV §3 |
| `Virtual/Extras.lean` | `kunen_in_model` | Kunen 1971; Kanamori Cor. 23.14, applied inside a transitive model of ZFC |
| `Sandwich.lean` | `amenable_dichotomy` | Goldberg, *Strongly compact cardinals and ordinal definability*, JML 24(1) 2024, arXiv:2107.00513v1, Lemma 2.7 (with §2.2) |
| | `ground_not_eventually_measurable` | Jech, Thm 15.3 (chain condition preserves cardinals) with Lemma 10.4 (measurables are inaccessible), applied in the ground |
| `Foundations/Witness.lean` | `critSeq_cofinal` | ABL §2 (restriction of an exact embedding is an I3 embedding); Kunen 1971; Kanamori Cor. 23.14 |
| `Width.lean` | `no_short_cofinal_OD` | ABL, arXiv:2411.11568v4, Thm 2.10 |
| `HODBoundary.lean` | `HOD_isInnerModelZF` | Jech, Thm 13.26 |

ABL = Aguilera–Bagaria–Lücke, arXiv:2411.11568v4.  BG = Goldberg (with Blue), *Consistency
beyond the Kunen inconsistency*, lecture notes, 1 July 2026,
<https://math.berkeley.edu/~goldberg/Slides/CoverExact.pdf>.  Goldberg = *The uniqueness of
elementary embeddings*, JSL 89 (2024); the numbers are those of arXiv v2 (the journal
version is reported to be shifted by one in §4).  Full bibliographic data is in the header
of `Published.lean` and in each doc comment.  The numbers for ABL, BG and Goldberg (both papers) were
checked against the PDFs on 18 September 2026; textbook citations are at chapter/section
level where the exact number was not checked.

The barrier is derived from BG's stationary characterization (the synthesis' "Route S").  Blue–Goldberg's
Theorem 3.6 is *not* admitted: it is re-derived as `no_CEx_above_extendible`.

`Audit.lean` confirms that the fully proved theorems depend only on `propext`,
`Classical.choice`, `Quot.sound`, and that the others add only `sorryAx`.

## Coverage

| Synthesis | Lean | Status |
|---|---|---|
| Def. 2.1–2.3 | `Foundations/Basic.lean`, `Foundations/Exacting.lean` | concrete definitions in `ZFSet` (`RelWitness`, `REx`, `CEx`, `Ex`, `CD`, `HCD`, `SC`, `Extendible`, clubs in `P_κ(A)`, inner models) |
| Lemma 3.1 (dynamics), 3.2 (last step) | `OrdinalLemmas.moved_above_crit`, `no_fixed_cofinal_set` | proved; the statements about witnesses themselves are admitted as known |
| Lemma 4.3 trace reconstruction | `trace_reconstruction`, `ElemSub.diff_mem`, `ElemSub.separate`, `Completeness.exists_seed`, `unique_of_trace` | **proved**, with the explicit defining formula |
| Lemma 4.4 singular endpoint | `Completeness.isComplete_succ_of_isSingular`, `IsCompleteUF.succ_of_isSingular` | **proved** (type level and `ZFSet` level) |
| Theorem 5.1 (1)–(4), Cor. 5.3 | `absorption`, `barrier`, `barrier_above`, `regular_in_HCD`, `cover_gap`, `barrier_singular`, `regular_in_HCD_self` | proved from admitted inputs |
| Cor. 5.5 | `finite_trace_of_regularIn`, `OrdinalLemmas.finite_inter_of_bounded` | proved |
| Theorem 6.1 + refinements | `separation`, `separation_no_small_cover`, `separation_no_refinement`, `separation_ultrafilter`, `cofinality_gap` | proved from admitted inputs |
| Cor. 6.2 | `P1 … P7`, `conditional_inconsistency`, `not_P4`, `not_P5`, `not_P7` | proved |
| Cor. 6.3 | `no_CEx_above_extendible` | proved (not admitted) |
| Theorem 6.4 | `first_regularization`, `RegularIn_HCD_mono`, `not_RegularIn_HCD_of_le` | proved |
| Lemma 7.1 | `OrdinalLemmas.countable_union_bounded` (core); `Published.cc_preserves_regular` | core proved; forcing theorem admitted as textbook |
| Theorem 7.2, Cor. 7.3–7.5 | `proper_ground`, `groundAxiom_obstruction`, `SC_le_cover_bound_of_GA`, `no_CEx_of_GA_of_class_SC`, `general_ground_obstruction`, `HCD_ground_not_cc`, `strongLimit_in_class`, `two_strongly_compacts` | proved from admitted inputs; forcing, grounds and `GA` are defined concretely |
| Theorem 8.1, Cor. 8.2 | `proj_OD`, `sups_OD`, `projection_width`, `card_family_ge` | **proved** from ABL Thm 2.10 (definability by explicit formulas) |
| Prop. 8.3, Theorem 10.7 (1)–(4) | `HODBoundary.lean` | proved from ABL Thm 2.10 |
| Lemma 9.1(b), Theorem 9.4 | `FiniteCycles.no_equivariant_selectors`, `Ultraexacting.no_preserved_finite_family` | **proved** over the elementarity facts used (hypotheses) |
| Lemma 9.7, Theorem 9.8, Cor. 9.9 (core) | `FiniteLabel.image_realize`, `disjoint_realize`, `exists_fixed_label`, `invariant_subset_of_transitive_perm`, `FiniteCycles.label_fixed` | **proved** over the elementarity facts used; uniform construction `a_i = {κ_n + π⁻ⁿ(i)}` |
| Theorem 9.10 | `Ultraexacting.no_finite_valued_transversal` | **proved** over the elementarity facts used |
| Lemma 10.3 (invariance) | `Ultraexacting.cloud_index_eq` | proved |
| Theorem 11.2, Cor. 11.3 | `Range.no_internal_unbounded_range`, `final_segment_not_in_range` | **proved** from the published HKP lemma (hypothesis) |

| Lemma 8.4(a) (second edition) | `SecondRound.fixed_small_set_below_crit` | **proved** (combinatorial core) |
| Lemma 12.11 cyclic stabilizers | `SecondRound.isCyclic_map_snd` | **proved** |
| Theorem 12.7 full phase; two-sided orbits | `SecondRound.eq_univ_of_image_succ_eq`, `two_sided_orbit_lt_crit`, `two_sided_orbit_const` | **proved** |

| Theorem 7.11 (amenable grounds cover), 7.12 (no sandwich), Cor. 7.13(a) | `amenable_ground_cover`, `countableCover_contra`, `amenable_ground_cof`, `no_sandwich`, `no_SC_above`; `ThirdRound.card_le_of_disjoint_meeting` | proved from Goldberg's Lemma 2.7 (admitted) with the amenability of `HCD(η)` (Lemma 7.10) as a **hypothesis**; shows that the hypotheses of `two_strongly_compacts` are inconsistent |
| Theorem 13.2, 13.3 (tail decisions, normality; cores) | `ThirdRound.orbit_mem_iff`, `orbit_decided`, `orbit_value_const`, `small_range_const`, `regressive_const_on_critical_sequence`, `tail_ultra` | **proved** (combinatorial core) |
| Theorem 13.9 (charges; cores) | `ThirdRound.phase_balance`, `no_two_valued_phase`, `mean_shift`, `tail_mean_indep` | **proved** |
| Section 14 (Prikry model; cores) | `FourthRound.fixed_of_insertion`, `finiteChange_realize_insert` (insertion rotates block-coded tuples), `shift_ne`, `no_finite_invariant`, `residue_law`; the finite algebra of Theorem 14.5 is `FiniteCycles.no_equivariant_selectors` | **proved** (combinatorial cores; no forcing is formalized) |
| Research note, Def. 2.1-2.2 (virtual / L-exacting witnesses) | `TWitness` over a transitive set `A` with the embedding **not** required to be in `A`; `RelWitness.toTWitness`, `toT_crit`, `toT_critSeq`, `cofinalType_toTWitness` (`Virtual/TWitness.lean`) | **proved**: the genuine notion is the special case `A = V_ α` |
| Research note, Theorem 3.1 (Kunen-free core) over a transitive model | `TWitness.jOrd_nat`, `jOrd_omega`, `omega_le_crit`, `jv_subset_fixed`, `no_surj_pow_crit`, `slSem_critSeq`, `crit_regular` (`Virtual/Core.lean`) | **proved** with all sizes internal to `A` (`powA`, `SurjSem`), so it applies to countable `A`; audit shows no `sorryAx` |
| Research note, Theorem 5.1(2),(3) (cofinal type) | `TWitness.fixed_small_subset`, `no_small_fixed_family`, `no_small_definable_family`, `least_surj_fixed` (`Virtual/Core.lean`) | **proved** from `CofinalType` as a hypothesis in place of the Kunen inconsistency |
| Research note, Lemma 2.3 (absoluteness), combinatorial core | `elementary_iff_assignment`, `exists_free_bound`, `assignment_iff_branch` (`Virtual/Extras.lean`) | **proved**: an embedding of a countable structure is a branch of a tree of finite approximations. The two-model absoluteness step is a metatheorem, not formalizable in one universe |
| Research note, Theorem 6.1(3) and Prop. 7.1 (cores) | `TWitness.restrictTo`, `no_fixed_point_of_minimal`, `exists_root` (`Virtual/Extras.lean`) | **proved** |
| Research note, Theorem 3.1(4) (the restriction to `V_lam^A` is elementary) | `relTo`, `relTo_spec` (relativization of a `Form` to a variable), `TWitness.vA_fixed`, `vA_lam_fixed`, `fixed_below_crit`, `restriction_elementary`, `restriction_moves_crit` (`Virtual/Restriction.lean`) | **proved**, one admitted input (definability of the cumulative hierarchy).  No satisfaction predicate inside `A` is needed: elementarity is formula-by-formula, so `relTo` suffices |
| Research note, Theorem 5.1(3) (`lam` regular in the definable model) | `no_short_cofinal_low_rank`, `no_small_family_low_rank`, `TWitness.fixed_param`, `least_ordinal_fixed` with `leastF`/`leastF_spec` (`Virtual/Regularity.lean`) | **proved** for parameters of rank below `lam` (which includes every ordinal `< lam`) and `lam` itself; nothing admitted in the file, but it inherits the hierarchy input through `fixed_below_crit`.  A witness is chosen *after* the parameter (`HasHighWitnesses`), which makes the parameter fixed.  `least_ordinal_fixed` is the least-counterexample device and is itself free of admitted statements; it fixes an ordinal parameter of *any* size |
| Research note, Theorem 4.1(1) (virtually exacting cardinals in `L`) | `SilverData` (the interface: levels of `L`, Silver indiscernibles, hulls, shift embeddings, each field cited), `SilverData.witness`, `witness_crit`, `witness_critSeq`, `witness_cofinalType`, `virtually_exacting_cofinal`, `hasHighWitnesses`, `crit_inaccessible_in_L`, `no_short_cofinal_in_L` (`Virtual/Constructible.lean`) | **derived** from the interface, nothing further admitted (`no_short_cofinal_in_L` inherits the hierarchy input through Theorem 5.1(3)).  Assuming `SilverData` is assuming `0^#`.  Theorem 4.1(2) (bounded type at `i_γ`, `γ > ω`) is not derived: the interface is specialized to `λ = i_ω`; the consistency statement 4.1(3) is metamathematical |
| Research note, Theorem 6.1(2),(4) | `StableData` (least stable ordinal + `Σ₁`-reflection, cited), `StableData.least_LExacting_lt_stable`, `LExacting_of_silver`, `LExacting` | **derived** from the interface |
| Research note, Theorem 6.1(1) | `TWitness.HasGraphIn`, `Published.lExacting_absolute` | admitted (Shoenfield absoluteness), with the complexity computation left to the reader |
| Research note, Prop. 5.3 | `TWitness.IsUltra`, `cofinalType_of_ultra` (`Virtual/Extras.lean`) | proved from the admitted in-model Kunen inconsistency |
| Section 15, Proposition 15.3 (Baire-measurable classification at λ = ω) | `Countable.zero_one` (topological zero-one law), `generic_const`, `fixed_label`, `Cantor.transitive`, `Cantor.global_fixed_point`, `Klein.separation` (`Countable/GenericErgodicity.lean`) | **proved**, nothing admitted; uses Mathlib's Baire category library |
| Research note *Exacting embeddings of countable structures*, Theorem 3.1 (Kunen-free core) and Prop. 7.1 | `RelWitness.crit_regular`, `cof_iff`, `interleave` (`KunenFree.lean`); with `jOrd_nat`, `jOrd_omega`, `jv_subset_fixed`, `no_surj_pow_crit`, `slSem_critSeq` | **proved**, and the audit shows no dependence on `critSeq_cofinal`: the critical points of a witness are inaccessible without the Kunen inconsistency, so the proofs apply to virtual witnesses |
| Lemma 3.1 (λ uncountable, cofinality ω, strong limit), for every exacting witness | `RelWitness.jOrd_nat`, `omega_le_crit`, `aleph0_lt`, `jv_subset_fixed`, `no_surj_pow_crit`, `slSem_critSeq`, `strongLimit` (`WitnessFacts.lean`) | **proved** from the Kunen inconsistency; formerly admitted |
| Lemma 3.2 = Blue–Goldberg Observation 1(2) | `RelWitness.trace_fixed`, `not_REx_shortCofinal` (`ObservationOne.lean`) | **proved**; formerly admitted.  Uses a formula of the language with the predicate, written directly in Mathlib's syntax |
| Lemma 3.5 (`γ ≥ λ`) | `RelWitness.jOrd_omega`, `trace_fixed_of`, `pow_lam_fixed`, `cntUnion_iff`, `le_of_CEx` (`CoverBound.lean`) | **proved**; formerly admitted |
| **Actual embedding:** elementarity for `Form`; Lemma 3.1 | `Bridge.realize_toLex`, `RelWitness.sat_j`, `elem`, `tarski_vaught`, `definable`, `definable_fixed`; `jOrd`, `crit`, `critSeq`, `le_jOrd`, `moved`, `fixed_iff_lt_crit` | **proved** from the definition of a witness (cofinality of the critical sequence admitted) |
| Lemma 8.4(a),(b) for the actual embedding | `RelWitness.fixed_small_subset`, `no_small_fixed_family` (with `exists_surj`, `least_surj_fixed`, `surj_iff`, `card_sUnion_le`) | **proved**; (b) for families with a common size bound `ν < λ`, which covers subfamilies of `D_λ` |
| Lemma 12.1(2) orbits | `RelWitness.IsUltra`, `orb`, `orb_mem_X`, `jv_eq_image`, `jv_orb`, `cofinalIn_orb`, `orb_locally_finite` | **proved** from `j ↾ V_λ ∈ X` |
| Theorem 12.3 / Cor. 12.4(1) zero-or-full traces, for sets fixed by `j` | `RelWitness.zero_or_full` (with `agree_iff`, `agree_in_X`, `evAgree_orb_shift`) | **proved**; the class is represented by eventual agreement with the orbit, which coincides with `=*` on `D_λ` |
| Theorem 9.10 / Cor. 12.5 for the actual embedding | `RelWitness.trace_eq_empty_of_card_lt`, `no_fixed_transversal` (`Transversals.lean`) | **proved** (for sets fixed by `j`) |
| Theorem 13.2 for the actual embedding | `RelWitness.tail_decision`, `regressive_const` | **proved** |

The numbering refers to the fourth edition of the synthesis, in which all earlier numbers
are unchanged; Sections 12-14 and the appended parts of Sections 7 and 8 are otherwise
not formalized.

### Not formalized

* The constructible hierarchy itself.  Neither Mathlib nor ProveIt has `L`, so
  `Virtual/Constructible.lean` supplies an *interface* -- the structures `SilverData`
  and `StableData`, whose fields are the published facts about `L`, the Silver
  indiscernibles and the least stable ordinal, each with its citation -- and derives
  Theorems 4.1(1) and 6.1(2),(4) of the note from it.  Building `L` and proving those
  fields is a separate project.
* Theorem 4.1(2) of the note (witnesses of bounded type at `i_γ` for limit `γ > ω`):
  the interface is specialized to `λ = i_ω`.  Theorem 4.1(3) is a consistency
  statement, hence metamathematical.
* The absoluteness step of Lemma 2.3 of the note (a branch of a tree exists in the
  smaller model): a metatheorem about two models of ZFC, not expressible inside one.

* Section 14 beyond its combinatorial cores: Prikry forcing, the cone isomorphisms and
  the insertion lemma, ground capture, the `2^κ` rigid classes, the countable families of
  Theorem 14.7, and all equiconsistency statements.  Neither Mathlib nor ProveIt has a
  forcing library.
* The phase theorem 12.7 for the actual embedding (the index `ind_a(b)` is not defined
  in `Orbits.lean`); its combinatorial core is `SecondRound.eq_univ_of_image_succ_eq`.

* The passage from *ordinal definable from `V_λ ∪ {q}`* to *fixed by `j`* (height
  correctness, the minimal-rank-parameter device, the canonical least counterexample).
  `zero_or_full`, `no_small_fixed_family` and `tail_decision` are stated for sets `T ∈ X`
  with `j(T) = T`; `RelWitness.definable_fixed` supplies this for every set definable over
  `V_α` from fixed parameters.

* Lemma 7.10 (amenability of `HCD(η)`): it needs the first-order definability of the class
  `HCD(η)` via reflection.  It enters `no_sandwich` as the hypothesis
  `OmegaClubAmenable (HCD η)`.  Goldberg's Lemma 2.7 is admitted rather than re-proved by
  the stationary-seed argument of Theorem 7.11.
* Section 13 beyond its combinatorial cores: the models `HOD_{d,q}`, Prikry genericity
  (Mathias' criterion), Theorem 13.6, the Vopěnka algebra, and the consistency-strength
  calibration of Theorem 13.7 (metamathematical, from Prikry forcing and Dodd–Jensen).

* Lemmas 3.3–3.5, 4.1–4.2 (Route H: persistent covers and exact hulls).  The barrier is
  obtained through Route S instead; these statements are covered by the admitted
  Blue–Goldberg inputs.
* The derivation of the elementarity facts of §9 from a formal definition of
  ultraexactingness (Lemmas 9.2, 9.3, the flat coding before Lemma 9.7, and the coding of
  Theorem 9.6, whose combinatorial core is again `no_preserved_finite_family`).
* Theorem 10.1 (cover exactingness from `I3_wf(0)`) beyond the invariance of the cloud:
  the internalization tree argument and the Prikry-forcing localization.
* All equiconsistency statements (Cor. 10.5, 10.6, Theorem 10.7 as a whole): they are
  metamathematical and imported from the literature.
