# Independent mathematical audit

**Reviewer role:** `/root/independent_search`, independent source-search and proof-audit agent.  
**Date:** 20 October 2026.  
**Scope:** Sections 2–6 of the main investigation report, the self-vacuity proof note, the finite Hilbert certificate, and the pinned imported decoder/soundness definitions. This is an ordinary mathematical and source-code review, not a new Lean/Rocq kernel check.

## Findings and required corrections

1. **Use the exact inherited decoder.** `KDecoder230.v` defines
   `T0 = Wim (Wal 0 (Weq 0 0)) (Wal 0 (Weq 0 0))`, a syntactically closed tautology. Code zero decodes to `T0`. In a positive implication-tag code with unpaired fields `(x,y)`, the case `y=1` decodes as primitive negation `Wn (D x)`, while other cases decode as `Wim (D x) (D y)`. An unspecialized decoder with zero represented by `R(0,0)→R(0,0)` is mathematically usable after a separate equivalence argument, but it is not literally this inherited decoder. The report should use the exact one.

2. **Self-freshness is already inherited.** `Sound230.v` proves `D_fr v n : fr v (D n)=true -> v<n` and `D_fr_self c : fr c (D c)=false`, including code zero. The positive-code bound on all occurring labels also follows by the stated strong induction, adding the special negation case. The new contribution is the one-parameter self-vacuity replacement and its recovery of unrestricted classicality; the code-self-freshness observation itself must be credited to the inherited development.

3. **K/S decoding uses the IR comparison theory.** Literal decoding of native K/S instances need not be a pure logical theorem. For example, native `K(1,1)` decodes to `FF→¬FF`, where `FF` is `x0∈x0`. `Sound230.D_wim_E` transports native implications to ordinary implications in the comparison theory. Its consequent-code-1 case uses `E_F`, which uses `V_nF` and therefore the comparison theory's irreflexivity axiom. The new K/S interpretation cases should explicitly use this equivalence. SV itself decodes literally to `D(n)→∀n D(n)`, since its quantifier-code consequent is neither 0 nor 1; it is a pure logical theorem by self-freshness. Weak SV decodes literally to its double negation by `D_wn`.

4. **“Closed” describes the derivation.** Generalization requires an assumption-free theorem derivation. It does not require the theorem's formula to have no free object-variable labels. The report's deduction argument uses the rule correctly; its definition should make this wording explicit.

## Positive audit conclusions

The persistence-to-stability derivation is correct using K, S, rho1, rho2 and rho6. Explosion and seriality have the stated finite derivations. From `NN(A→Q_i A)` one obtains the assumption-free theorem `A→NN(Q_i A)`, then `Q_i A→Q_i NN(Q_i A)`. With `Z=Q_i N(Q_i A)`, normality and seriality give `Z→N(Q_i A)` and hence `Z→NA`. Intuitionistic reasoning gives `NNA→NZ`; rho6 is exactly `NZ→A`.

Choosing `i=A` is legitimate at every natural code and recovers DNE in either self-vacuity variant. The subsequent derivation recovers all four unrestricted parameters of the old rho8 row. Numerical aliases only identify expressions and do not invalidate a proof that uses no constructor-injectivity assumption. Generalization is applied only after temporary hypotheses have been discharged.

The supplied 1,110-node finite Hilbert certificate was rerun successfully. Its independent serialized rule reader checks rule instances, backwards dependencies and open-assumption sets. It shares axiom-formula definitions with the builder, so it is not an independent formalization of those definitions.

Both consistency directions are sound ordinary extensions of the pinned C222 calibration after the decoder corrections above. The lower direction replaces each old rho8 axiom in a finite native refutation by the new finite derivation. The upper direction extends the inherited proof induction in `thm222_V`, uses exact decoder compatibility and the new logical SV cases, and then reuses the existing refutation translations. The target code 1 decodes to self-membership and is refuted using IR. This does not require theorem-set equality of the native calculi, a transitive model, or an unconditional model of ZFC.

## Remaining proof level

The new label-bound/application arguments and the extended upper interpretation are ordinary mathematical proofs formalizable in ZFC. The additional SV/K/S cases have not been submitted to a Lean or Rocq kernel. The finite Hilbert replay proves the lower schematic derivations; it does not by itself prove the inherited set-theoretic translations, emitter correctness, arbitrary-register tape simulation, or blank initialization. No 217-state blank-tape candidate follows from this audit.

## Pinned primary sources

All files below were retrieved from ProveIt commit `9adcaff0a72486ecc81242e0eca86e428c74879e` and their local bytes were checked against the returned Git blob identifiers. `provenance.json` records both SHA-256 and Git blob SHA-1.

- [KDecoder230.v](https://github.com/VladimirReshetnikov/ProveIt/blob/9adcaff0a72486ecc81242e0eca86e428c74879e/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/117-k226dp-vendor-k230-rocq-coq-settheory-KDecoder230.v)
- [Sound230.v](https://github.com/VladimirReshetnikov/ProveIt/blob/9adcaff0a72486ecc81242e0eca86e428c74879e/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/117-k226dp-vendor-k230-rocq-coq-logic-Sound230.v)
- [L1_LDef.v](https://github.com/VladimirReshetnikov/ProveIt/blob/9adcaff0a72486ecc81242e0eca86e428c74879e/lib/jeff-busy-beaver-zfc254/ZF/stdzf/coq/L1_LDef.v)

## Additional initialized-core review

The delivered `core217/check_core.py`, its recorded runtime receipt, and the inherited symbolic engine were also reviewed. The driver verifies the exact deletion/three-row construction, complete 217-state/434-row census, injective legacy-state relabelling, all 6,167 guarded source cases, positive duration, and full transition-row coverage. The symbolic engine's unary and finite-list rules are justified by their table-checked schemas; its 4,000-rule proof-construction bound is not a bound on actual runtime or register values. Its frame domain includes nine arbitrary natural register values, an arbitrary natural extra gap, one arbitrary first spare, and an arbitrary finite remaining spare list. The requirement that a first spare exists is retained in the report's scope.

I independently reran the quick exact construction/blank check, including the accepted K218 positive control. It passed: the core reaches state 35, head 7, with exactly the one-cells {-3,-2} after 85 steps, and row 35/0 then proves the infinite rightward ray by induction. The report correctly distinguishes this failure from the initialized interface theorem. I did not repeat the already completed full 114-second runtime replay during this review; the source review and the recorded complete replay are the evidence for that part.
