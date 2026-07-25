import ZFCinPA.TarskiFieldSemantics

/-!
# Audit for the two Tarski field bundles and their soundness

Three layers are kept visible in their types:

* the compound code shapes the bundles are stated over;
* the two bundles `TarskiElim` (eight clauses) and `TarskiIntro` (nine
  clauses), of an arbitrary ternary relation;
* their truth of goal 2's real level predicates — the two strong
  quantifier eliminations, which goal 2 does not export, and the two
  bundle-level theorems `tarskiElim_levelSat`/`tarskiIntro_levelSat`.

The soundness statements are what `ZFCinPA.BaseCertificate` consumes, so
an axiom leak here would silently become an axiom leak in the base
certificate.
-/

namespace LeanProofs.ZFCinPA.TarskiFieldSemanticsAudit

open LeanProofs.ZFCinPA.EnlargedFields

/-! ## Code shapes -/

#check @botC
#check @impC
#check @andC
#check @orC
#check @allC
#check @exC

/-! ## The two bundles -/

#check @TarskiElim
#check @TarskiIntro

/-! ## Soundness -/

#check @sigmaTrue_all_elim_strong
#check @piFalse_ex_elim_strong
#check @tarskiElim_levelSat
#check @tarskiIntro_levelSat

/-! ## Assumption audit

The repository's semantic core is classical, so `Classical.choice`,
`propext` and `Quot.sound` are expected; nothing beyond Lean's three
standard axioms should appear, and in particular no `sorry` and no
theory-specific axiom. -/

#print axioms sigmaTrue_all_elim_strong
#print axioms piFalse_ex_elim_strong
#print axioms tarskiElim_levelSat
#print axioms tarskiIntro_levelSat

end LeanProofs.ZFCinPA.TarskiFieldSemanticsAudit
