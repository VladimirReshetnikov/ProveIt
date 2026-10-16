import GowersSzemeredi.Definitions

/-!
Integer representatives of modular progressions.

`ModAP.IsProper` certifies injectivity of the parameterization, not absence
of a crossing of the boundary of `[0,N)`. The distinction matters in
Lemmas 5.12--5.13 and in the integer interpretation of Section 16 boxes.
We retain the existing predicate and introduce a separate geometric one.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The carrier has a genuine positive-step progression of integer
representatives in `[0,N)`, of the same length. Reversing the ordering is
allowed: this is a property of the set rather than its parameterization. -/
def ModAP.HasIntegerRepresentatives {N : Nat} (P : ModAP N) : Prop :=
  ∃ Q : NatAP, Q.IsProper ∧ Q.length = P.length ∧
    Q.carrier ⊆ Finset.range N ∧
    Q.carrier.image (fun x : Nat => (x : ZMod N)) = P.carrier

/-- Reducing the coordinates of an ordinary progression modulo `N`. -/
def NatAP.toModAP (N : Nat) (Q : NatAP) : ModAP N :=
  ⟨Q.start, Q.step, Q.length⟩

theorem NatAP.toModAP_carrier (N : Nat) (Q : NatAP) :
    (Q.toModAP N).carrier = Q.carrier.image (fun x : Nat => (x : ZMod N)) := by
  simp only [NatAP.toModAP, ModAP.carrier, NatAP.carrier, Finset.image_image]
  apply Finset.image_congr
  intro i _
  simp

theorem NatAP.toModAP_hasIntegerRepresentatives {N : Nat} (Q : NatAP)
    (hQ : Q.IsProper) (hsub : Q.carrier ⊆ Finset.range N) :
    (Q.toModAP N).HasIntegerRepresentatives :=
  ⟨Q, hQ, rfl, hsub, (Q.toModAP_carrier N).symm⟩

/-- Integer representatives imply carrier-based properness, over any
nonzero modulus. No primality hypothesis is needed. -/
theorem ModAP.HasIntegerRepresentatives.isProper {N : Nat} [NeZero N]
    {P : ModAP N} (hP : P.HasIntegerRepresentatives) : P.IsProper := by
  obtain ⟨Q, hQ, hlen, hsub, himage⟩ := hP
  have hinj : Set.InjOn (fun x : Nat => (x : ZMod N)) (Q.carrier : Set Nat) := by
    intro x hx y hy heq
    have hxN := Finset.mem_range.mp (hsub hx)
    have hyN := Finset.mem_range.mp (hsub hy)
    have hval := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast_of_lt hxN, ZMod.val_natCast_of_lt hyN] using hval
  rw [ModAP.IsProper, ← himage, Finset.card_image_iff.mpr hinj, hQ.2, hlen]

/-- The integer progression can be recovered exactly by taking canonical
representatives of the modular carrier. -/
theorem ModAP.HasIntegerRepresentatives.val_carrier {N : Nat} [NeZero N]
    {P : ModAP N} (hP : P.HasIntegerRepresentatives) :
    ∃ Q : NatAP, Q.IsProper ∧ Q.length = P.length ∧
      P.carrier.image ZMod.val = Q.carrier := by
  obtain ⟨Q, hQ, hlen, hsub, himage⟩ := hP
  refine ⟨Q, hQ, hlen, ?_⟩
  rw [← himage, Finset.image_image]
  calc
    Q.carrier.image (ZMod.val ∘ fun x : Nat => (x : ZMod N)) =
        Q.carrier.image id := by
      apply Finset.image_congr
      intro x hx
      exact ZMod.val_natCast_of_lt (Finset.mem_range.mp (hsub hx))
    _ = Q.carrier := Finset.image_id

/-- A simple sufficient condition for the specified orientation to have
integer representatives: all its unreduced terms lie below the modulus. -/
theorem NatAP.toModAP_hasIntegerRepresentatives_of_bound {N : Nat}
    (Q : NatAP) (hstep : 0 < Q.step)
    (hbound : ∀ i : Nat, i < Q.length → Q.start + i * Q.step < N) :
    (Q.toModAP N).HasIntegerRepresentatives := by
  apply Q.toModAP_hasIntegerRepresentatives
  · refine ⟨hstep, ?_⟩
    unfold NatAP.carrier
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij
      apply Fin.ext
      exact Nat.mul_right_cancel hstep (Nat.add_left_cancel hij)
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hbound i i.isLt)

/-- A three-term progression with distinct residues which crosses the
canonical boundary. Its representative set is `{0,1,6}`, not an integer AP. -/
def wrappingThreeTermAP : ModAP 7 := ⟨6, 1, 3⟩

theorem wrappingThreeTermAP_carrier :
    wrappingThreeTermAP.carrier = {0, 1, 6} := by
  decide

theorem wrappingThreeTermAP_isProper : wrappingThreeTermAP.IsProper := by
  unfold ModAP.IsProper
  decide

/-- Injectivity of modular indices does not imply the geometric
properness required by the paper's integer-representative convention. -/
theorem wrappingThreeTermAP_noIntegerRepresentatives :
    ¬ wrappingThreeTermAP.HasIntegerRepresentatives := by
  rintro ⟨Q, hQ, hlen, hsub, himage⟩
  have hlen3 : Q.length = 3 := hlen
  have hterm (i : Nat) (hi : i < 3) :
      Q.start + i * Q.step < 7 ∧
        (Q.start + i * Q.step = 0 ∨ Q.start + i * Q.step = 1 ∨
          Q.start + i * Q.step = 6) := by
    have hmem : Q.start + i * Q.step ∈ Q.carrier := by
      exact Finset.mem_image.mpr ⟨⟨i, by omega⟩, Finset.mem_univ _, rfl⟩
    have hlt := Finset.mem_range.mp (hsub hmem)
    have hmod : ((Q.start + i * Q.step : Nat) : ZMod 7) ∈
        wrappingThreeTermAP.carrier := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨_, hmem, rfl⟩
    rw [wrappingThreeTermAP_carrier] at hmod
    have hvals : (((Q.start + i * Q.step : Nat) : ZMod 7)).val ∈
        ({0, 1, 6} : Finset (ZMod 7)).image ZMod.val := Finset.mem_image.mpr
      ⟨((Q.start + i * Q.step : Nat) : ZMod 7), hmod, rfl⟩
    have hval : (((Q.start + i * Q.step : Nat) : ZMod 7)).val =
        Q.start + i * Q.step := ZMod.val_natCast_of_lt hlt
    rw [hval] at hvals
    change Q.start + i * Q.step ∈ ({0, 1, 6} : Finset Nat) at hvals
    exact ⟨hlt, by simpa only [Finset.mem_insert, Finset.mem_singleton] using hvals⟩
  have h1 := hterm 1 (by omega)
  have h2 := hterm 2 (by omega)
  have hstep := hQ.1
  omega

theorem modAP_isProper_does_not_imply_integerRepresentatives :
    ¬ (∀ P : ModAP 7, P.IsProper → P.HasIntegerRepresentatives) := by
  intro h
  exact wrappingThreeTermAP_noIntegerRepresentatives
    (h wrappingThreeTermAP wrappingThreeTermAP_isProper)

end LeanProofs.GowersSzemeredi
