import BusyBeaver.ZFC.KDecoderPrefix215
import BusyBeaver.ZFC.KHomeReady

/-! Adapted from the preserved phase9 uncompiled CB1Suffix proposal.
A finite unchanged-word witness turns the q1 return into one all-frame theorem.
The actual CB1 family retains the complete prefix A, not just its last two bits.
See the accompanying compilation receipt for the validation status. -/
namespace SetTheory.BusyBeaver.ZFC.KCB1Suffix
open KZip KRuntimeCore KSim KDecoderPrefix215

/-- Check exactly a leftward unchanged-word traversal.  The final marker is
part of the checked word, so A=[] reaches the boundary without a special case. -/
def leftCheck (M : TMN) : Nat → List Bool → Nat → Bool
  | q, [], q' => decide (q = q')
  | q, b :: word, q' =>
    match M q b with
    | some (w, false, r) => decide (w = b) && leftCheck M r word q'
    | _ => false

theorem leftCheck_sound {M : TMN} {q q' : Nat} {word : List Bool}
    (h : leftCheck M q word q' = true) : KHome.LeftWord M q word q' := by
  induction word generalizing q with
  | nil =>
    have he : q = q' := by simpa only [leftCheck, decide_eq_true_eq] using h
    subst q'
    exact .nil _
  | cons b word ih =>
    cases ht : M q b with
    | none => simp [leftCheck, ht] at h
    | some t =>
      obtain ⟨w, dir, r⟩ := t
      cases dir with
      | true => simp [leftCheck, ht] at h
      | false =>
        have hh : w = b ∧ leftCheck M r word q' = true := by
          simpa only [leftCheck, ht, Bool.and_eq_true, decide_eq_true_eq] using h
        obtain ⟨rfl, hr⟩ := hh
        exact .cons ht (ih hr)

/-- A q1 return, including the marker read, followed by the already-proved
blank-left boundary.  R is completely arbitrary and is never inspected. -/
theorem return1 {M : TMN} (hb : KHome.Boundary M) (A R : List Bool)
    (hw : KHome.LeftWord M 1 (A.reverse ++ [true]) 2) :
    Reach1 M (zl 1 (A.reverse ++ [true]) R) (zc 84 [true] (A ++ R)) := by
  have hs := hw.sound [] R
  have he : Reach M (zl 1 (A.reverse ++ [true]) R)
      (zl 2 [] (true :: (A ++ R))) := by
    simpa only [List.append_nil, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.reverse_reverse, List.nil_append,
      List.singleton_append, List.append_assoc, List.cons_append] using hs
  exact he.trans_reach1 (hb (A ++ R))

/-- The common CB1 suffix: the three steps rewrite A001 to A100, then q1
returns over the unchanged A.  This preserves every possible right frame R. -/
theorem cb1_frame {M : TMN}
    (h108 : M 108 true = some (false, false, 10))
    (h10 : M 10 false = some (false, false, 16))
    (h16 : M 16 false = some (true, false, 1))
    (hb : KHome.Boundary M) (A R : List Bool)
    (hw : KHome.LeftWord M 1 (A.reverse ++ [true]) 2) :
    Reach1 M (zc 108 (false :: false :: (A.reverse ++ [true])) (true :: R))
      (zc 84 [true] (A ++ (true :: false :: false :: R))) := by
  have h1 : Reach1 M
      (zc 108 (false :: false :: (A.reverse ++ [true])) (true :: R))
      (zc 10 (false :: (A.reverse ++ [true])) (false :: false :: R)) := by
    apply Reach1.of_step
    simpa only [zl_cons] using
      (zL (l := false :: false :: (A.reverse ++ [true])) (r := R) h108)
  have h2 : Reach M
      (zc 10 (false :: (A.reverse ++ [true])) (false :: false :: R))
      (zc 16 (A.reverse ++ [true]) (false :: false :: false :: R)) := by
    apply Reach.of_step
    simpa only [zl_cons] using
      (zL (l := false :: (A.reverse ++ [true])) (r := false :: R) h10)
  have h3 : Reach M
      (zc 16 (A.reverse ++ [true]) (false :: false :: false :: R))
      (zl 1 (A.reverse ++ [true]) (true :: false :: false :: R)) :=
    Reach.of_step (zL (l := A.reverse ++ [true]) (r := false :: false :: R) h16)
  exact (h1.trans_reach (h2.trans h3)).trans_reach
    (return1 hb A (true :: false :: false :: R) hw).reach

/-- The exact old CB1 target, for all gap parameters and register lists.  There
is no BoxLemmas premise or validity/length condition on vs: no box is touched. -/
theorem cb1_leafPort {M : TMN}
    (h108 : M 108 true = some (false, false, 10))
    (h10 : M 10 false = some (false, false, 16))
    (h16 : M 16 false = some (true, false, 1))
    (hb : KHome.Boundary M) (A : List Bool)
    (hw : KHome.LeftWord M 1 (A.reverse ++ [true]) 2)
    (hlen : A.length + 3 ≤ D0) (n : Nat) (vs : List Nat) :
    Reach1 M (conc n vs (leafPort (A ++ [false, false]) true 108))
      (conc n vs (tgtConf (A ++ [true]) false (.plain .none))) := by
  have hgap : n + (D0 - (A.length + 3)) + 2 = n + (D0 - (A.length + 1)) := by omega
  have hr := cb1_frame h108 h10 h16 hb A
    (List.replicate (n + (D0 - (A.length + 3))) false ++ true :: sepsR vs) hw
  have hs : conc n vs (leafPort (A ++ [false, false]) true 108) =
      zc 108 (false :: false :: (A.reverse ++ [true]))
        (true :: (List.replicate (n + (D0 - (A.length + 3))) false ++ true :: sepsR vs)) := by
    simp only [conc_leafPort, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.length_append, List.length_cons,
      List.length_nil, List.append_assoc, Nat.add_assoc, Nat.zero_add]
  have ht : conc n vs (tgtConf (A ++ [true]) false (.plain .none)) =
      zc 84 [true] (A ++ (true :: false :: false ::
        (List.replicate (n + (D0 - (A.length + 3))) false ++ true :: sepsR vs))) := by
    rw [conc_target]
    simp only [growth, boxList, Bool.false_eq_true, if_false, Nat.add_zero,
      List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
      List.append_assoc, List.singleton_append]
    rw [← hgap]
    simp only [List.replicate_succ, List.cons_append]
  rw [hs, ht]
  exact hr


end SetTheory.BusyBeaver.ZFC.KCB1Suffix
