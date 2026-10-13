# Generators of the Fejér-route modules (Notes L.16d–L.16e)

Most modules of the Fejér route are copies of corpus modules with the
printed θ₁, Bohr radius, Lemma 15.6 threshold and class degree replaced.
These scripts made the copies. Each one reads its corpus original(s),
applies exact-string and word-boundary substitutions, and asserts a guard
regex that no printed name survives (`section16ThetaOne`, `section16Zeta`,
`lemma156ExplicitThreshold`, `globalBudget`, `stepP`, `uDeg68`, …).
The substitutions are the record of how a copy differs from its original,
which is what the planned fold-in refactor needs (notes L.16e, "Refactor
map").

| script | output module(s) | original(s) |
|---|---|---|
| `assemble_fejer.py` | `Proofs15FejerSelection` | `Proofs15Restriction` (+ hand-written Fejér part) |
| `assemble_fejer156.py` | `Proofs15FejerProduct` | `Proofs15ProductToRestriction` (+ hand-written part) |
| `assemble_l5with.py` | `Proofs16Lemma5With` | `Proofs16Lemma5`, `Proofs16ArrangementSelection` |
| `assemble_dswith.py` | `Proofs16DenseSelectionWith` | `Proofs16DenseSelection`, `Proofs16CommonBase`, … |
| `assemble_pptwith.py` | `Proofs16PolyPieceTwoDataWith` | `Proofs16PolyPieceTwoData` |
| `assemble_pctfejer.py` | `Proofs16PolyCoverTwoFejer` | `Proofs16PolyCoverTwo` |
| `assemble_seedexp.py` | `Proofs18FejerSeedExponents` | `Proofs18LengthSixCounts`, `…Exponents` |
| `assemble_uctfejer.py` | `Proofs16UniformCoverTwoFejer` | `Proofs16UniformCoverTwo(Bounds)`, `Proofs16PowerUniformClass` |
| `assemble_cpwith.py` | `Proofs16ClassPiecesWith` | `Proofs16ClassPieces` |
| `assemble_csfejer.py` | `Proofs16ClassStepFejer` | `Proofs16ClassStep` |
| `assemble_csdfejer.py` | `Proofs16ClassStepDegreesFejer` | `Proofs16ClassStepDegrees` |
| `assemble_ssfejer.py` | `Proofs16SplitStepFejer` | `Proofs16SplitStepBounds` (+ hand-written recursion) |
| `assemble_spcgw.py` | `Proofs16SinglePieceCoverGlobalWith` | `Proofs16SinglePieceCoverGlobal` |
| `assemble_spcinvf.py` | `Proofs18SinglePieceCoverInverseFejer` | `Proofs18SinglePieceCoverInverse` |
| `assemble_coverf.py` | `Proofs18Cover{Modulus,Density,Exponents}Fejer` | `Proofs18Cover{Modulus,Density,Exponents}` |
| `assemble_headf.py` | `Proofs18CoverFejerHeadline` | `Proofs18CoverDegrees`, `…TightBase`, `…ThresholdsSharp` (+ hand-written closed forms) |
| `mk_fejer_low_short.py` | `Proofs18CoverFejerLowDegrees`, `…ShortLengths` | `Proofs18CoverSharperLowDegrees`, `Proofs18CoverThresholdsSharp` |
| `mk_low5_short3.py` | `Proofs18CoverFejerLowDegrees5`, `…ShortLengths3` | `Proofs18CoverFejerLowDegrees` (6 ↦ 5), `Proofs18CoverFejerShortLengths` (4 ↦ 3) |
| `assemble_l163sharp.py` | `Proofs16BaseCaseRestrictionSharp` | `Proofs16BaseCaseRestriction` |
| `assemble_febq.py` | `Proofs18FejerEnvelopeBaseQ` | `Proofs18GenericEnvelopeBase` (atom `2^(k+5)` ↦ `5k+14`) |
| `assemble_coverq.py` | `Proofs18Cover{Modulus,Density,Exponents}FejerQ` | the `…Fejer` modules (`uDegQ`, `fixDegQ`) |
| `assemble_headq.py` | `Proofs18CoverFejerHeadlineQ` | `Proofs18CoverFejerHeadline` (+ hand-written closed forms) |
| `assemble_polyq.py` | `Proofs16PolynomialFejerQ` | `Proofs16PolynomialFejer` |
| `assemble_etasmall.py` | `Proofs18EtaStepSmall` | `Proofs18GenericDensity` (`fixDeg k ≤ m` ↦ `3(k+4)² ≤ m`) |
| `assemble_s.py` | `Proofs18Cover{Modulus,Density,Exponents}FejerS`, `Proofs18CoverFejerHeadlineS` | the `…FejerQ` modules (`uDegS`, `sDeg`, η via `eta_step_small`); headline head/tail in `headline_s_{head,tail}.lean.txt` |
| `assemble_t.py` | `Proofs18Cover{Modulus,Density,Exponents}FejerT`, `Proofs18CoverFejerHeadlineT` | the `…FejerS` modules (`uDegT`, `tDeg`, η side condition from `sq_le_fixDegQ`); headline head/tail in `headline_t_{head,tail}.lean.txt` |
| `assemble_u.py` | `Proofs18CoverFejerHeadlineU` | `MReq_le_expT`/`Tloc_le_expT` (`Z = 5k+21`, `threshDegU`) and the Theorem 18.2 recursion of `Proofs18CoverFejerHeadlineT`; head/tail in `headline_u_{head,tail}.lean.txt` |
| `assemble_basew.py` | `Proofs18FejerEnvelopeBaseW` | `slice_const_le`, `uCount_scale_le` (any degree `b ≥ 7`), `baseCFQ_recipPowerLB` (at `pDeg`); hand-written parts `basew_{head,fixed,tail}.lean.txt` |
| `assemble_w.py` | `Proofs18Cover{Modulus,Density,Exponents}FejerW`, `Proofs18CoverFejerHeadlineW` | the T chain with `fixDegQ ↦ pDeg`, the U threshold, polynomial `hconst`; `headline_w_{hyp,head,tail}.lean.txt` |
| `assemble_x.py` | `Proofs18Cover{Modulus,Density,Exponents}FejerX`, `Proofs18CoverFejerHeadlineX` | the W chain at `tDegX` with the polynomial Lemma 15.6 threshold; `headline_x_{head,tail}.lean.txt` |
| `assemble_polys.py` | `Proofs16PolynomialFejerS` | `Proofs16PolynomialFejerQ` (reuses the renames of `assemble_s.py`) |
| `assemble_polyf.py` | `Proofs16PolynomialFejer` | `Proofs16PolynomialStructure`, `…Corollary` |
| `assemble_jslice.py` | `Proofs16JointSliceCell` | `Proofs16SinglePieceSpectrum`'s line-cell lemma with the two anchor slices covered jointly (`joint_cover_on`, `E = {a, b}`) |
| `assemble_jspec.py`, `assemble_jcore.py` | `Proofs16JointSliceSpectrum`, `Proofs16JointSliceCore` | the affine-cell / spectrum-cover lemmas and `single_piece_lift_core_rem` with slice covers |
| `assemble_jglob.py` | `Proofs16JointSliceGlobal` | `single_piece_lift_global_cover_with` with translated slice covers |
| `assemble_jinv.py` | `Proofs18JointSliceInverseFejer` | `Proofs18SinglePieceCoverInverseFejer` with the `…FJ` density, width, scale and modulus conditions |
| `assemble_j.py` | `Proofs18Cover{Modulus,Density,Exponents}FejerJ` | the Z chain over the joint-slice inverse step: `GenParamsJ`, `Eth = Ec = E(θ_S/4)`, `GenParams.joint_dens_step`, `densDegJ = ρ + tDeg + 11` |
| `assemble_jy.py` | `Proofs18CoverFejerHeadlineJ` | the Y (Theorem 18.1) and Z (Theorem 18.2) envelopes over the J step, new closed forms and kernel fits |
| `mk_low4.py` | `Proofs18CoverFejerLowDegrees4` | `Proofs18CoverFejerLowDegrees5` with `5 ↦ 4` |
| `patch_bridge_j.py` | the joint-slice block of `Proofs18CoverFejerAllDegrees` and `CompletionAudit.lean` | — |
| `assemble_k.py` | `Proofs18CoverFejerHeadlineK` | `inv_thr_le_ex` and the J Theorem 18.2 step with the partition constant at `partDeg k = (k+3)² + (k+2)(k+1)` (`polyPartConst_le_sharp`) |
| `patch_bridge_k.py` | the sharp-partition block of `Proofs18CoverFejerAllDegrees` and `CompletionAudit.lean` | — |
| `assemble_polyj.py` | `Proofs16PolynomialFejerJ` | `Proofs16PolynomialFejerX` at `tDegZ` with the joint-slice frequency box (`expDegJ_tight_le`, `singlePieceEtaFJ_le_density`) |
| `patch_bridge_polyj.py` | the 16.2 / 16.11 block of `Proofs18CoverFejerAllDegrees` and `CompletionAudit.lean` | — |
| `assemble_m.py` | `Proofs18TightClassesFejerM` | the Fejér split step combined by `max` (`splitStepAMax`, `splitStepDMaxF`), its invariants, the exact table `tDegM` to 14 |
| `assemble_jm.py` | `Proofs18Cover{Modulus,Density,Exponents}FejerJM`, `Proofs18CoverFejerHeadlineJM` | the J chain over `tDegM` (identifier-level renames), Theorem 18.1 at `d + 2` from 11 |
| `patch_m.py` | the max-step block of `Proofs18CoverFejerAllDegrees`, `CompletionAudit.lean`, notes, status, TeX | — |
| `assemble_jt.py`, `jt_head.lean.txt`, `jt_thm.lean.txt` | `Proofs18Cover{Modulus,Density,Exponents}FejerJT`, `Proofs18CoverFejerHeadlineJT` | the J chain over the two-track classes `tDegT2`, Theorem 18.1 at `d + 3` from 8 (`Proofs16SplitTwoTrack*` are hand-written) |
| `patch_t2.py` | the two-track block of `Proofs18CoverFejerAllDegrees`, `CompletionAudit.lean`, notes, status, TeX | — |
| `assemble_tight.py` | `Proofs16UniformCoverTwoTight` | the dimension-two face count at the unrounded exponent `10002·(2^23+1)`, the count at `W^(2^39)`, the tight two-track seed |
| `assemble_t3.py` | `Proofs16SplitTwoTrackClassesT3` | the two-track recursion from the tight seed, the table `tDegT3` |
| `assemble_k3.py` | `Proofs18Cover{Modulus,Density,Exponents}FejerJT3`, `Proofs18CoverFejerHeadlineK3` | the J chain and the K (Theorem 18.2) envelope over `tDegT3`, `L + 0` from 13 |
| `patch_k3.py` | the tight-count block of `Proofs18CoverFejerAllDegrees`, `CompletionAudit.lean`, notes, status, TeX | — |
| `assemble_polyt3.py`, `patch_polyt3.py` | `Proofs16PolynomialFejerT3` and its bridge block | Theorem 16.2 / Corollary 16.11 at `tDegT3` |
| `final_extract.py`, `assemble_final.py` | `Proofs18FinalClasses`, `Proofs18FinalStep`, `Proofs18FinalEnvelopes`, `Proofs18Final` | the final route (notes L.16-final): the declarations the final bounds use, extracted from the variant modules in their original order, the Theorem 18.1 step over `tDegT3` (renamed from the JT step), the fits, and `FinalInputs` |
| `retire.py`, `audit_final_section.lean.txt` | deletes the 63 variant modules, rewrites the facade, the bridge, `IntegerOriginalCorollaryFidelityAudit` and the final-route block of `CompletionAudit.lean` | — |
| `mkstub_final.py` | stub check of the new bridge and audit block | — |
| `mkstub_fejer18.py`, `mkstub_auditfejer.py` | stub checks of `Proofs18CoverFejerAllDegrees` and the Fejér block of `CompletionAudit.lean` | — |

Hand-written modules (no generator): `Proofs15WalshGeneral`,
`Proofs15DegenerateRange`, `Proofs16TightRadius`, `Proofs16SplitFejerDegrees`,
`Proofs18FejerSeedCounts`, `Proofs16ClassStepBoundsFejer`,
`Proofs18TightClassesFejer`, `Proofs18TightClassesFejerQ`, `Proofs18TightClassesFejerS`, `Proofs18TightClassesFejerT`, `Proofs18TightClassesFejerX`,
`Proofs16UniformCoverTwoSplit`, `Proofs18FejerEnvelopeBase` and the bridge
`Proofs18CoverFejerAllDegrees`.

Since the final route (notes L.16-final), the variant chains generated above
(suffixes Q, S, T, U, W, X, Z, Y, J, JM, JT, JT3, K, K3, and the generated low-degree
and short-length variants) no longer exist; their scripts document how the
route was reached. The unsuffixed base modules and the joint-slice modules
remain.

Caveats:
* The scripts hard-code the worktree path where they ran, and some outputs
  were edited by hand after generation (compile fixes). The committed
  modules are authoritative; the scripts document the substitutions.
* Two scripts read session-local inputs that are not committed: the
  hand-written Fejér parts of `assemble_fejer.py` / `assemble_fejer156.py`
  (now contained in the output modules), and `StubAll18.lean` for the stub
  checks. That file states the heavy corpus theorems as axioms, so it is
  deliberately kept out of the repository.
