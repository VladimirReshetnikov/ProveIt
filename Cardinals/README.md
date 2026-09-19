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
source in the docstring.  There are 18 of them; nothing else uses `sorry`.

| File | Admitted statement | Reference |
|---|---|---|
| `Published.lean` | `cof_omega_of_witness`, `strongLimit_of_witness` | ABL, remark after Def. 2.4; Kunen 1971; Kanamori Cor. 23.14 |
| | `aleph0_lt_of_witness` | ABL §2 (restriction is an I3 embedding); Kanamori §5, §24 |
| | `not_REx_shortCofinal` | BG, Observation 1(2) |
| | `REx_transfer` | BG, Lemma 3.3 |
| | `le_of_CEx` | BG, remark after Def. 3.1 |
| | `stationary_of_CEx` | BG, Proposition 3.4 (1)⇒(3) |
| | `isClub_elemSub` | Jech Ch. 8 (clubs in P_κ(A)) and Ch. 12; Kanamori §25 |
| | `ODfrom_trans` | Jech Ch. 13 (ordinal-definable sets), Thm 12.14 (reflection) |
| | `SC_of_extendible` | Kanamori Prop. 23.6, §22; Jech Ch. 20 |
| | `HCD_isInnerModelZF`, `HCD_isInnerModelZFC`, `HCD_cover`, `HCD_stabilizes` | Goldberg, arXiv:2103.13961v2, Prop. 4.2, Thm 4.3, Thm 4.13, Thm 4.14 |
| `Above.lean` | `HCD_isGround` | Goldberg, arXiv:2103.13961v2, Thm 4.9 |
| | `cc_preserves_regular` | Kunen 1980, Ch. VII Lemma 6.9; Jech Ch. 15 |
| `Width.lean` | `no_short_cofinal_OD` | ABL, arXiv:2411.11568v4, Thm 2.10 |
| `HODBoundary.lean` | `HOD_isInnerModelZF` | Jech, Thm 13.26 |

ABL = Aguilera–Bagaria–Lücke, arXiv:2411.11568v4.  BG = Goldberg (with Blue), *Consistency
beyond the Kunen inconsistency*, lecture notes, 1 July 2026,
<https://math.berkeley.edu/~goldberg/Slides/CoverExact.pdf>.  Goldberg = *The uniqueness of
elementary embeddings*, JSL 89 (2024); the numbers are those of arXiv v2 (the journal
version is reported to be shifted by one in §4).  Full bibliographic data is in the header
of `Published.lean` and in each doc comment.  The numbers for ABL, BG and Goldberg were
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

The numbering refers to the second edition of the synthesis, in which all first-edition
numbers are unchanged; the new Section 12 and the appended parts of Sections 7 and 8 are
otherwise not yet formalized.

### Not formalized

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
