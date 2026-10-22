import BusyBeaver.ZFC.KSim

/-!
Compose a shared decoder prefix with an independently checked primitive suffix.
The prefix may have zero physical length. Every nonhalting suffix must make
positive progress, and its target is exactly the original site target.

This module adds no concrete suffix certificates and removes no site cases.
-/
namespace SetTheory.BusyBeaver.ZFC.KSimPrefix

open KZip KRuntimeCore KSim RegisterPath SiteCoverage RMBisim

/-- One fixed symbolic entry works uniformly for every gap and register list. -/
def PrefixSpec (M : TMN) (Q : List Bool) (entry : SConf) : Prop :=
  ∀ (n : Nat) (vs : List Nat),
    Reach M (conc n vs (start Q)) (conc n vs entry)

def RunFromSpec (M : TMN) (br : Branch) (entry target : SConf) : Prop :=
  ∀ (n : Nat) {vs : List Nat}, Valid br vs →
    Reach1 M (conc n vs entry) (conc n vs target)

def HaltFromSpec (M : TMN) (entry : SConf) : Prop :=
  ∀ (n : Nat) {vs : List Nat}, 10 ≤ vs.length →
    ∃ c, Reach M (conc n vs entry) c ∧ c.q = 230

def runToFrom (M : TMN) (br : Branch) (entry target : SConf) : Bool :=
  (KHomeReady.exec M br (fun s => sMatches s target) FUEL entry false).isSome

def runHaltFrom (M : TMN) (entry : SConf) : Bool :=
  (KHomeReady.exec M none isHalt FUEL entry false).isSome

theorem runToFrom_sound {M : TMN} (B : BoxLemmas M) {br : Branch}
    {entry target : SConf} (h : runToFrom M br entry target = true) :
    RunFromSpec M br entry target := by
  intro n vs hv
  unfold runToFrom at h
  cases hx : KHomeReady.exec M br (fun s => sMatches s target) FUEL entry false with
  | none => rw [hx] at h; simp at h
  | some s =>
    obtain ⟨hm, _, h1⟩ := KHomeReady.exec_sound B n hv FUEL entry false s hx
    rw [← sMatches_conc n vs hm]
    exact h1 rfl

theorem runHaltFrom_sound {M : TMN} (B : BoxLemmas M) {entry : SConf}
    (h : runHaltFrom M entry = true) : HaltFromSpec M entry := by
  intro n vs hv
  unfold runHaltFrom at h
  cases hx : KHomeReady.exec M none isHalt FUEL entry false with
  | none => rw [hx] at h; simp at h
  | some s =>
    obtain ⟨hh, h0, _⟩ :=
      KHomeReady.exec_sound B n (br := none) ⟨hv, trivial⟩ FUEL entry false s hx
    refine ⟨_, h0, ?_⟩
    obtain ⟨q, onl, l, r⟩ := s
    simp only [isHalt, beq_iff_eq] at hh
    cases onl <;> simpa [conc, zl, zc] using hh

theorem runToSpec_of_prefix {M : TMN} {br : Branch} {Q : List Bool}
    {entry target : SConf} (hp : PrefixSpec M Q entry)
    (hs : RunFromSpec M br entry target) : RunToSpec M br Q target := by
  intro n vs hv
  exact (hp n vs).trans_reach1 (hs n hv)

theorem haltPortSpec_of_prefix {M : TMN} {Q : List Bool} {entry : SConf}
    (hp : PrefixSpec M Q entry) (hs : HaltFromSpec M entry) : HaltPortSpec M Q := by
  intro n vs hv
  obtain ⟨c, hc, hq⟩ := hs n hv
  exact ⟨c, (hp n vs).trans hc, hq⟩

/-- The original branch obligations, with execution starting at `entry`.
The entire consumed word Q still determines the target and its overflow. -/
def checkEdgeFrom (M : TMN) (Q : List Bool) (entry : SConf) : Edge → Bool
  | .inc r => decide (Q.length ≤ 48) && decide (r < 9) &&
      runToFrom M none entry (tgtConf (incPath Q) (allOnes Q) (.plain (.inc (physOf r))))
  | .decnz r => decide (Q.length ≤ 48) && decide (r < 9) &&
      runToFrom M (some (physOf r, true)) entry
        (tgtConf (breakPath 1 Q) (allOnes (stripPath false 1 Q)) (.plain .none)) &&
      runToFrom M (some (physOf r, false)) entry
        (tgtConf (incPath Q) (allOnes Q) (.plain (.dec (physOf r))))
  | .brk k => decide (Q.length ≤ 48) &&
      runToFrom M none entry
        (tgtConf (breakPath k Q) (allOnes (stripPath false k Q)) (.plain .none))
  | .cont k => decide (Q.length ≤ 48) &&
      runToFrom M none entry (tgtConf (continuePath k Q) false (.plain .none))
  | .halt => decide (Q.length ≤ 48) && runHaltFrom M entry
  | .node _ => false

/-- A checked suffix and a proved prefix establish the semantic site contract.
This theorem needs no terminal-row premise; it retains the old halt-port API. -/
theorem edgeSpec_of_prefix_checked {M : TMN} (B : BoxLemmas M)
    {Q : List Bool} {entry : SConf} {e : Edge} (hp : PrefixSpec M Q entry)
    (h : checkEdgeFrom M Q entry e = true) : KSim.EdgeSpec M Q e := by
  cases e with
  | inc r =>
    simp only [checkEdgeFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, runToSpec_of_prefix hp (runToFrom_sound B h.2)⟩
  | decnz r =>
    simp only [checkEdgeFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1, h.1.1.2,
      runToSpec_of_prefix hp (runToFrom_sound B h.1.2),
      runToSpec_of_prefix hp (runToFrom_sound B h.2)⟩
  | brk k | cont k =>
    simp only [checkEdgeFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, runToSpec_of_prefix hp (runToFrom_sound B h.2)⟩
  | halt =>
    simp only [checkEdgeFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, haltPortSpec_of_prefix hp (runHaltFrom_sound B h.2)⟩
  | node k => simp [checkEdgeFrom] at h

/-- Finite tree totality and a contract at every exact leaf give coverage of
all inputs, including implicit zero padding of consumed source words. -/
theorem semanticCovered_of_leaf_specs {M : TMN} {p : Program} {t : Tree}
    (ht : ptree p = t)
    (total : allSites (fun _ _ => true) [] t = true)
    (leaves : ∀ {Q e}, LeafAt t Q e → KSim.EdgeSpec M Q e) :
    SemanticCovered M p := by
  intro P
  obtain ⟨e, d, hw⟩ := allSites_walk_total (fun _ _ => true) p t ht total P
  have hwalk : twalk t P 0 = some (e, d) := by
    simpa only [← ht, ← walk_root] using hw
  have hl := (twalk_leafAt t P 0 e d hwalk).2
  have leaf : LeafAt t (consume P d) e := by
    simpa only [Nat.sub_zero, RMEquiv.consume_eq] using hl
  exact ⟨e, d, hw, leaves leaf⟩

/-- The compatibility start is a zero-length prefix. -/
theorem prefix_refl (M : TMN) (Q : List Bool) : PrefixSpec M Q (start Q) :=
  fun _ _ => Reach.refl M _

theorem checkEdgeFrom_start (M : TMN) (Q : List Bool) (e : Edge) :
    checkEdgeFrom M Q (start Q) e = checkEdge M Q e := by
  cases e <;> rfl

#print axioms runToFrom_sound
#print axioms runHaltFrom_sound
#print axioms edgeSpec_of_prefix_checked
#print axioms semanticCovered_of_leaf_specs

end SetTheory.BusyBeaver.ZFC.KSimPrefix
