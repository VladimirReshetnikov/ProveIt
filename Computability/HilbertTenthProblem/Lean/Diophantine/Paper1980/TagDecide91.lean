import Diophantine.Paper1980.TagUniversal91
import Mathlib.Computability.Halting

/-!
# The encoded instances of the tag certificate form an undecidable family

`tag91_re` makes membership in a recursively enumerable set the solvability of the 18 equations
at encoded instances.  Here the encoding is shown to be primitive recursive
(`CProgram.primrec_instance`: `x ↦ (γ_x, content W_x, 3^|W_x|)`), and, taking for `S` the
halting problem of Mathlib's partial recursive codes, the solvability of the certificate over
the family is not a computable predicate (`tag91_undecidable`).
-/

namespace Jones1980

open TagSys Nat.Partrec

/-! ### Primitive recursive building blocks -/

theorem primrec_replicate {σ : Type*} [Primcodable σ] (b : σ) :
    Primrec (fun n : ℕ => List.replicate n b) :=
  (Primrec.nat_iterate Primrec.id (Primrec.const []) ((Primrec.list_cons.comp (Primrec.const b)
    Primrec.snd).to₂)).of_eq fun n => by
    show (fun l : List σ => b :: l)^[n] [] = List.replicate n b
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem primrec_pow (c : ℕ) : Primrec (fun n : ℕ => c ^ n) :=
  (Primrec.nat_iterate Primrec.id (Primrec.const 1) ((Primrec.nat_mul.comp Primrec.snd
    (Primrec.const c)).to₂)).of_eq fun n => by
    show (fun y => y * c)^[n] 1 = c ^ n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ]

theorem content_eq_foldr (W : List Bool) : content W = W.foldr (fun b s => bit b + 3 * s) 0 := by
  induction W with
  | nil => rfl
  | cons b W ih => rw [content_cons, ih]; rfl

theorem primrec_content : Primrec content :=
  (Primrec.list_foldr Primrec.id (Primrec.const 0) ((Primrec.nat_add.comp
    ((Primrec.dom_bool bit).comp (Primrec.fst.comp Primrec.snd))
    (Primrec.nat_mul.comp (Primrec.const 3) (Primrec.snd.comp Primrec.snd))).to₂)).of_eq
    fun W => (content_eq_foldr W).symm

namespace DTag

variable (D : DTag)

theorem primrec_enc : Primrec D.enc :=
  (Primrec.list_append.comp
    ((primrec_replicate false).comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1))))
    (Primrec.list_cons.comp (Primrec.const true)
      ((primrec_replicate false).comp (Primrec.nat_sub.comp (Primrec.const D.L)
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_add.comp Primrec.id (Primrec.const 1))))))).of_eq fun _ => rfl

theorem primrec_itok : Primrec D.itok :=
  (Primrec.option_casesOn Primrec.id (Primrec.const [true])
    ((D.primrec_enc.comp Primrec.snd).to₂)).of_eq fun o => by cases o <;> rfl

theorem primrec_toks : Primrec D.toks :=
  (Primrec.list_flatMap Primrec.id ((D.primrec_itok.comp Primrec.snd).to₂)).of_eq fun _ => rfl

theorem primrec_bits : Primrec D.bits :=
  (Primrec.list_flatMap Primrec.id (((Primrec.dom_bool D.prodB).comp Primrec.snd).to₂)).of_eq
    fun _ => rfl

theorem primrec_W0 : Primrec D.W0 := by
  have hmap : Primrec (fun w : List ℕ => w.map some) :=
    Primrec.list_map Primrec.id ((Primrec.option_some.comp Primrec.snd).to₂)
  have hpad : Primrec D.pad :=
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const (D.β - 2))
      (Primrec.list_length.comp (D.primrec_bits.comp (D.primrec_toks.comp hmap))))
      (Primrec.const 1)).of_eq fun _ => rfl
  exact (D.primrec_bits.comp (D.primrec_toks.comp (Primrec.list_append.comp hmap
    ((primrec_replicate none).comp hpad)))).of_eq fun _ => rfl

end DTag

theorem GProg.primrec_tagWord : Primrec GProg.tagWord :=
  (Primrec.list_append.comp (Primrec.list_flatMap
    (Primrec.list_cons.comp (Primrec.const false) (primrec_replicate true))
    (((Primrec.dom_bool (GProg.bj 0)).comp Primrec.snd).to₂))
    (Primrec.const (GProg.blk 6 0))).of_eq fun _ => rfl

namespace CProgram

variable (M : CProgram)

/-- **The encoding of the instances is primitive recursive.** -/
theorem primrec_instance :
    Primrec (fun x => (M.binγ x, content (M.binWord x), 3 ^ (M.binWord x).length)) := by
  have hW : Primrec M.binWord :=
    ((M.compile).dtag.primrec_W0.comp (GProg.primrec_tagWord.comp (primrec_pow 2))).of_eq
      fun _ => rfl
  have hγ : Primrec M.binγ :=
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.list_length.comp hW) (Primrec.const (3 * M.binTS.β)))
      (Primrec.const M.binTS.u.length)) (Primrec.const 2)).of_eq fun _ => rfl
  exact Primrec.pair hγ (Primrec.pair (primrec_content.comp hW)
    ((primrec_pow 3).comp (Primrec.list_length.comp hW)))

end CProgram

/-- **Undecidability of the encoded tag family**: a fixed binary tag system, with a primitive
recursive encoding of inputs, for which solvability of the 18 equations is not computable. -/
theorem tag91_undecidable :
    ∃ M : CProgram,
      Primrec (fun x => (M.binγ x, content (M.binWord x), 3 ^ (M.binWord x).length)) ∧
      (∀ x, (tagConst M.binTS (M.binγ x)).Ok ∧ Matches (tagConst M.binTS (M.binγ x)) M.binTS) ∧
      ¬ ComputablePred (fun x => Solvable91 (tagConst M.binTS (M.binγ x))
        (content (M.binWord x)) (3 ^ (M.binWord x).length)) := by
  let S : ℕ → Prop := fun k => (Code.eval (Denumerable.ofNat Code k) 0).Dom
  have hS : REPred S :=
    (ComputablePred.halting_problem_re 0).comp (Computable.ofNat Code)
  obtain ⟨M, hM⟩ := tag91_re (S := {k | S k}) hS
  refine ⟨M, M.primrec_instance, fun x => ⟨(hM x).1, (hM x).2.1⟩, fun hc => ?_⟩
  apply ComputablePred.halting_problem 0
  have hS' : ComputablePred S :=
    ComputablePred.of_eq hc (fun x => ((hM x).2.2).symm)
  obtain ⟨inst, hcomp⟩ := hS'
  refine ⟨fun c => decidable_of_iff (S (Encodable.encode c)) (by simp [S]), ?_⟩
  exact (hcomp.comp Computable.encode).of_eq fun c => by simp [S]

end Jones1980
