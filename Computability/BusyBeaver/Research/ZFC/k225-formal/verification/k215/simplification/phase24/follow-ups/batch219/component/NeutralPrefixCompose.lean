import BusyBeaver.ZFC.KHomeReady

/-!
UNCOMPILED source-only component, separate from phase24 production sources.
Adapts proof-spine's neutral-prefix composition argument, placed at
56b37bde8b064d852154ad8478d58ec9ab5375d6. No checker, cut predicate,
classifier, source trace, machine table or maintained API is changed.
-/
namespace SetTheory.BusyBeaver.ZFC.DecrementPrefixNextLead

open KZip KRuntimeCore

/-- A neutral prefix supplies progress; its specialized continuation may be reflexive. -/
theorem neutral_prefix_compose {M : TMN} (B : BoxLemmas M)
    {cut target : SConf → Bool} {br : Branch} {f g : Nat} {s c t : SConf}
    (hp : KHomeReady.exec M none cut f s false = some c)
    (ht : KHomeReady.exec M br target g c true = some t)
    (n : Nat) {vs : List Nat} (hv : Valid br vs) :
    target t = true ∧ Reach1 M (conc n vs s) (conc n vs t) := by
  have hn : Valid none vs := ⟨hv.1, trivial⟩
  obtain ⟨_, _, hprefix⟩ := KHomeReady.exec_sound B n hn f s false c hp
  obtain ⟨hmatch, htail, _⟩ := KHomeReady.exec_sound B n hv g c true t ht
  exact ⟨hmatch, (hprefix rfl).trans_reach htail⟩

#print axioms neutral_prefix_compose
end SetTheory.BusyBeaver.ZFC.DecrementPrefixNextLead
