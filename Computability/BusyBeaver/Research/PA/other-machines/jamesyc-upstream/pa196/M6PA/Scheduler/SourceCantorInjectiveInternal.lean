module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.SourceCantorDecodeInvariant
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.SourceCantorInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem triangle_strict_below (b : V) : ∀ a<b, triangleValue a < triangleValue b := by
  induction b using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro a ha; simp at ha
  case succ b ih =>
    intro a ha
    have hab : a≤b := (le_iff_lt_succ).mpr ha
    have hstep : triangleValue b < triangleValue (b+1) := by
      rw [triangle_succ]
      exact lt_of_le_of_lt (show triangleValue b ≤ triangleValue b+b by simp) (lt_add_one _)
    by_cases he : a=b
    · simpa only [he] using hstep
    · exact lt_trans (ih a (lt_of_le_of_ne hab he)) hstep

theorem triangle_mono {a b : V} (h : a≤b) : triangleValue a≤triangleValue b := by
  by_cases he : a=b
  · simp [he]
  · exact le_of_lt (triangle_strict_below b a (lt_of_le_of_ne h he))

theorem triangle_ge (n : V) : n ≤ triangleValue n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [triangle_succ]
    calc
      n+1 ≤ triangleValue n+1 := by simpa only [add_comm] using add_le_add_right ih 1
      _ ≤ triangleValue n+n+1 := by simpa only [add_comm] using add_le_add_right (show triangleValue n ≤ triangleValue n+n by simp) 1

theorem pairValue_lower (a b : V) : triangleValue (a+b) ≤ pairValue a b := by
  simp [pairValue]
theorem pairValue_upper (a b : V) : pairValue a b < triangleValue (a+b+1) := by
  rw [triangle_succ]
  have hb : b<a+b+1 := lt_of_le_of_lt (show b≤a+b by simp) (lt_add_one _)
  simpa only [pairValue,add_assoc,add_comm,add_left_comm] using add_lt_add_left hb (triangleValue (a+b))

/-- Injectivity holds uniformly in nonstandard models as well. -/
theorem pairValue_injective {a b c d : V} (h : pairValue a b = pairValue c d) : a=c ∧ b=d := by
  have hs : a+b=c+d := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hm := triangle_mono ((succ_le_iff_lt).mpr hlt)
      have hh := lt_of_lt_of_le (pairValue_upper a b) (le_trans hm (pairValue_lower c d))
      exact (ne_of_lt hh) h
    · have hm := triangle_mono ((succ_le_iff_lt).mpr hgt)
      have hh := lt_of_lt_of_le (pairValue_upper c d) (le_trans hm (pairValue_lower a b))
      exact (ne_of_lt hh) h.symm
  have hb : b=d := by
    apply add_left_cancel (a := triangleValue (a+b))
    simpa only [pairValue,hs] using h
  have ha : a=c := by
    exact add_right_cancel (show a+b=c+b from by simpa only [hb] using hs)
  exact ⟨ha,hb⟩

theorem decode_pairValue (a b : V) :
    decodeLeft (pairValue a b)=a ∧ decodeRight (pairValue a b)=b :=
  pairValue_injective (pairValue_decode (pairValue a b))

theorem pairValue_bounds (a b : V) : a≤pairValue a b ∧ b≤pairValue a b := by
  have hh := le_trans (triangle_ge (a+b)) (pairValue_lower a b)
  exact ⟨le_trans (by simp) hh,le_trans (by simp) hh⟩

theorem decodeValue_bounds (n : V) : decodeLeft n≤n ∧ decodeRight n≤n := by
  have hh := pairValue_bounds (decodeLeft n) (decodeRight n)
  rw [pairValue_decode] at hh
  exact hh

noncomputable def encodeDecodeSentence : ArithmeticSentence :=
  “∀ n a b, !pairGraph n a b → !decodeGraph a b n”

theorem pa_proves_encode_decode : theory ⊢ encodeDecodeSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [encodeDecodeSentence,models_iff]
  simp [decode_graph,pair_graph]
  intro n a b hn
  subst n
  exact ⟨(decode_pairValue a b).1.symm,(decode_pairValue a b).2.symm⟩

noncomputable def decodeBoundsSentence : ArithmeticSentence :=
  “∀ n a b, !decodeGraph a b n → a ≤ n ∧ b ≤ n”
theorem pa_proves_decode_bounds : theory ⊢ decodeBoundsSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [decodeBoundsSentence,models_iff]
  simpa [decode_graph] using (fun n : V => decodeValue_bounds n)

#print axioms pa_proves_decode_bounds

#print axioms pairValue_injective
#print axioms pa_proves_encode_decode
end M6.PA.SourceCantorInternal

