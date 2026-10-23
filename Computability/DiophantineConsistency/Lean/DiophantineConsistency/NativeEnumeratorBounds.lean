import DiophantineConsistency.NativeEnumerationSize
import Mathlib.Tactic.FinCases

/-! # A depth bound for the actual refutation-enumerator step

The fixed blocks are certified separately. All remaining estimates propagate
through the supplied graph constructors and the already checked witness count.
-/

namespace DiophantineConsistency.NativeEnumeratorBounds

open Rep (Thin)
open NativeEnumerationSize
open DirectGraphEnumerator (R)

attribute [local irreducible] Nat.unpair

private theorem tc (n : ℕ) : Thin allowance (DirectGraphEnumerator.constant n) :=
  GraphRep.thin_constant _ (by decide) n
private theorem ti : Thin allowance DirectGraphEnumerator.identity :=
  GraphRep.thin_coordinate _ (by decide) 0
private theorem ta {f g : ℕ → ℕ} (r : R f) (s : R g)
    (hr : Thin allowance r) (hs : Thin allowance s) : Thin allowance (DirectGraphEnumerator.add r s) :=
  GraphRep.thin_add _ _ _ hr hs
private theorem tsu {f : ℕ → ℕ} (r : R f) (hr : Thin allowance r) :
    Thin allowance (DirectGraphEnumerator.successor r) :=
  GraphRep.thin_add _ _ _ hr (GraphRep.thin_constant _ (by decide) 1)
private theorem tsub {f g : ℕ → ℕ} (r : R f) (s : R g)
    (hr : Thin allowance r) (hs : Thin allowance s) : Thin allowance (DirectGraphEnumerator.sub r s) := by
  unfold DirectGraphEnumerator.sub GraphRep.sub
  apply GraphRep.thin_compose _ (by decide) (by decide) _ _ subCoordinates_thin
  intro i
  fin_cases i <;> assumption
private theorem tcomp {f g : ℕ → ℕ} (r : R f) (s : R g)
    (hr : Thin allowance r) (hs : Thin allowance s) : Thin allowance (DirectGraphEnumerator.comp r s) := by
  exact GraphRep.thin_compose _ (by decide) (by decide) _ _ hr (fun _ => hs)
private theorem tcompD {f g : ℕ → ℕ} (r : R f) (s : R g)
    (hr : Thin allowance r) (hs : Thin allowance s) : Thin allowance (NativeGraphEnumerator.comp r s) := by
  exact GraphRep.thin_composeDirect _ (by decide) (by decide) _ _ hr (fun _ => hs)
private theorem teq {f g h k : ℕ → ℕ} (r : R f) (s : R g) (t : R h) (u : R k)
    (hr : Thin allowance r) (hs : Thin allowance s) (ht : Thin allowance t) (hu : Thin allowance u) :
    Thin allowance (NativeGraphEnumerator.ifEq r s t u) := by
  unfold NativeGraphEnumerator.ifEq GraphRep.ifEqDirect
  apply GraphRep.thin_composeDirect _ (by decide) (by decide) _ _ ifEqCoordinates_thin
  intro i
  fin_cases i <;> assumption
private theorem tzero {f g h : ℕ → ℕ} (r : R f) (s : R g) (t : R h)
    (hr : Thin allowance r) (hs : Thin allowance s) (ht : Thin allowance t) :
    Thin allowance (NativeGraphEnumerator.ifZero r s t) :=
  teq _ _ _ _ hr (tc 0) hs ht
private theorem tul {f : ℕ → ℕ} (r : R f) (hr : Thin allowance r) :
    Thin allowance (NativeGraphEnumerator.unpairLeft r) :=
  GraphRep.thin_composeDirect _ (by decide) (by decide) _ _ cantorLeftCoordinate_thin (fun _ => hr)
private theorem tur {f : ℕ → ℕ} (r : R f) (hr : Thin allowance r) :
    Thin allowance (NativeGraphEnumerator.unpairRight r) :=
  GraphRep.thin_composeDirect _ (by decide) (by decide) _ _ cantorRightCoordinate_thin (fun _ => hr)
private theorem tcp {f g : ℕ → ℕ} (r : R f) (s : R g)
    (hr : Thin allowance r) (hs : Thin allowance s) : Thin allowance (NativeGraphEnumerator.cantorPair r s) := by
  unfold NativeGraphEnumerator.cantorPair
  apply GraphRep.thin_composeDirect _ (by decide) (by decide) _ _ cantorPairCoordinates_thin
  intro i
  fin_cases i <;> assumption
private theorem tnp {f g : ℕ → ℕ} (r : R f) (s : R g)
    (hr : Thin allowance r) (hs : Thin allowance s) : Thin allowance (NativeGraphEnumerator.naturalPair r s) := by
  unfold NativeGraphEnumerator.naturalPair
  apply GraphRep.thin_composeDirect _ (by decide) (by decide) _ _ naturalPairCoordinates_thin
  intro i
  fin_cases i <;> assumption
private theorem tim {f g : ℕ → ℕ} (r : R f) (s : R g)
    (hr : Thin allowance r) (hs : Thin allowance s) : Thin allowance (NativeGraphEnumerator.implication r s) := by
  unfold NativeGraphEnumerator.implication NativeFormulaGraphs.implication
  apply GraphRep.thin_composeDirect _ (by decide) (by decide) _ _ implicationCoordinates_thin
  intro i
  fin_cases i <;> assumption
private theorem tgate {f g h : ℕ → ℕ} (r : R f) (s : R g) (t : R h)
    (hr : Thin allowance r) (hs : Thin allowance s) (ht : Thin allowance t) :
    Thin allowance (NativeGraphEnumerator.gated r s t) := by
  unfold NativeGraphEnumerator.gated NativeFormulaGraphs.gated
  apply GraphRep.thin_composeDirect _ (by decide) (by decide) _ _ gateCoordinates_thin
  intro i
  fin_cases i <;> assumption
private theorem tstack {a h b c u t w : ℕ → ℕ}
    (ra : R a) (rh : R h) (rb : R b) (rc : R c) (ru : R u) (rt : R t) (rw : R w)
    (ha : Thin allowance ra) (hh : Thin allowance rh) (hb : Thin allowance rb)
    (hc : Thin allowance rc) (hu : Thin allowance ru) (ht : Thin allowance rt) (hw : Thin allowance rw) :
    Thin allowance (NativeGraphEnumerator.stack ra rh rb rc ru rt rw) := by
  unfold NativeGraphEnumerator.stack NativeFormulaGraphs.stack
  apply GraphRep.thin_composeDirect _ (by decide) (by decide) _ _ stackCoordinates_thin
  intro i
  fin_cases i <;> assumption
private theorem tstate {a b c d e f : ℕ → ℕ}
    (ra : R a) (rb : R b) (rc : R c) (rd : R d) (re : R e) (rf : R f)
    (ha : Thin allowance ra) (hb : Thin allowance rb) (hc : Thin allowance rc)
    (hd : Thin allowance rd) (he : Thin allowance re) (hf : Thin allowance rf) :
    Thin allowance (NativeGraphEnumerator.state ra rb rc rd re rf) := by
  exact tnp _ _ ha (tnp _ _ hb (tnp _ _ hc (tnp _ _ hd (tnp _ _ he hf))))

private theorem tnl : Thin allowance DirectGraphEnumerator.naturalLeft :=
  GraphRep.thin_compose _ (by decide) (by decide) _ _ naturalLeftCoordinate_thin
    (fun _ => GraphRep.thin_coordinate _ (by decide) 0)
private theorem tnr : Thin allowance DirectGraphEnumerator.naturalRight :=
  GraphRep.thin_compose _ (by decide) (by decide) _ _ naturalRightCoordinate_thin
    (fun _ => GraphRep.thin_coordinate _ (by decide) 0)

private theorem tpl : Thin allowance DirectGraphEnumerator.pl := tnl
private theorem tnpReg : Thin allowance DirectGraphEnumerator.np := tcomp _ _ tnl tnr
private theorem ttw : Thin allowance DirectGraphEnumerator.tw := tcomp _ _ tnl (tcomp _ _ tnr tnr)
private theorem tws : Thin allowance DirectGraphEnumerator.ws := tcomp _ _ tnl (tcomp _ _ tnr (tcomp _ _ tnr tnr))
private theorem tdepth : Thin allowance DirectGraphEnumerator.depth := by
  unfold DirectGraphEnumerator.depth
  exact tcomp _ _ tnl (tcomp _ _ tnr (tcomp _ _ tnr (tcomp _ _ tnr tnr)))
private theorem tcache : Thin allowance DirectGraphEnumerator.cache := by
  unfold DirectGraphEnumerator.cache
  exact tcomp _ _ tnr (tcomp _ _ tnr (tcomp _ _ tnr (tcomp _ _ tnr tnr)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem rawStepProgram_thin {a b : ℕ → ℕ} (ha : R a) (hb : R b)
    (hra : Thin allowance ha) (hrb : Thin allowance hb) :
    Thin allowance (NativeGraphEnumerator.rawStepProgram ha hb) := by
  dsimp only [NativeGraphEnumerator.rawStepProgram, DirectGraphEnumerator.ofEq]
  rw [Rep.thin_ofIff]
  have htag := tul ha hra
  have hrest := tur ha hra
  have hx := tul _ hrest
  have hy := tur _ hrest
  have hav := ta _ _ tdepth (tul _ hy)
  have hbval := ta _ _ tcache hx
  have hcv := tsub _ _ htag (tc 3)
  have hdv := ta _ _ tdepth hx
  exact teq _ _ _ _ htag (tc 0)
    (teq _ _ _ _ tcache (tc 1) (tc 0)
      (tsu _ (tstate _ _ _ _ _ _ hrest hrb ttw (tur _ tws) tdepth (tul _ tws))))
    (teq _ _ _ _ htag (tc 1)
      (tsu _ (tstate _ _ _ _ _ _ hrest hrb tcache (tcp _ _ ttw tws) tdepth tcache))
      (teq _ _ _ _ htag (tc 2)
        (teq _ _ _ _ (tim _ _ ttw hdv) tcache
          (tsu _ (tstate _ _ _ _ _ _ hy hrb hdv (tcp _ _ (tc 0) tws) hdv (tc 0)))
          (tsu _ (tstate _ _ _ _ _ _ hy hrb (tc 0) tws hdv (tc 0))))
        (tsu _ (tstate _ _ _ _ _ _ (tur _ hy) hrb (tgate _ _ _ hav hbval hcv)
          (tstack _ _ _ _ _ _ _ hav tcache hbval hcv tdepth ttw tws) (tc 0) (tc 0)))))


set_option maxRecDepth 10000 in
theorem enumStepProgram_thin : Thin allowance NativeGraphEnumerator.enumStepProgram := by
  dsimp only [NativeGraphEnumerator.enumStepProgram, DirectGraphEnumerator.ofEq]
  rw [Rep.thin_ofIff]
  apply rawStepProgram_thin
  · exact teq _ _ _ _ tpl (tc 0) tnpReg (tsub _ _ tpl (tc 1))
  · exact teq _ _ _ _ tpl (tc 0) (tsu _ tnpReg) tnpReg

theorem enumStepProgram_depth : NativeGraphEnumerator.enumStepProgram.depth ≤ 10964 := by
  have h := enumStepProgram_thin
  unfold Thin at h
  rw [NativeGraphEnumerator.enumStepProgram_witnessCount] at h
  exact h

set_option maxRecDepth 10000 in
theorem optionStepProgram_thin : Thin allowance NativeGraphEnumerator.optionStepProgram :=
  tzero _ _ _ ti (tc 0) (tcompD _ _ enumStepProgram_thin (tsub _ _ ti (tc 1)))

end DiophantineConsistency.NativeEnumeratorBounds
