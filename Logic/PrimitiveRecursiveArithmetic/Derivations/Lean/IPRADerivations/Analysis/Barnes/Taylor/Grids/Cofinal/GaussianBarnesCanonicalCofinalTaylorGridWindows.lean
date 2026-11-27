import IPRADerivations.Analysis.Barnes.Taylor.Grids.Cofinal.GaussianBarnesCanonicalCofinalTaylorGridObservations
import IPRADerivations.Analysis.Polynomials.FiniteDifferences.Grids.GaussianPolynomialForwardDifferenceGridIncrement

/-!
# Exact adjacent windows of the original cofinal Barnes observation grid

The signed numerator pairs agree at the translated grid nodes, so each
window is the original packed observation sequence at the same clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorGridWindows

open_ipra
open ComplexLogarithmRemainder (add code im re scale)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (cofinal_at cofinalData cofinalGrid)
open GaussianPolynomialForwardDifferenceGridIncrement (slice slice_at)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open LeanProofs.IPRA.Foundations.SequenceEquality (agree sequence_equal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem code_congr (x y u v : ZT n)
    (hr₁ : Γ ⊢[PRAAx] x.pos ≐ u.pos) (hr₂ : Γ ⊢[PRAAx] x.neg ≐ u.neg)
    (hi₁ : Γ ⊢[PRAAx] y.pos ≐ v.pos) (hi₂ : Γ ⊢[PRAAx] y.neg ≐ v.neg) :
    Γ ⊢[PRAAx] code x y ≐ code u v :=
  Common.congrPairT (Common.congrPairT hr₁ hr₂) (Common.congrPairT hi₁ hi₂)

private theorem add_scaled (z h j : PTm n) :
    Γ ⊢[PRAAx] add z (scale j h) ≐
      code (re z+ZT.ofNat j*re h) (im z+ZT.ofNat j*im h) := by
  let x := ZT.ofNat j*re h
  let y := ZT.ofNat j*im h
  let X := pairT x.pos x.neg
  let Y := pairT y.pos y.neg
  exact code_congr _ _ _ _
    (congrAdd (.eqRefl _) ((congrFst (fst_pair X Y)).eqTrans (fst_pair x.pos x.neg)))
    (congrAdd (.eqRefl _) ((congrSnd (fst_pair X Y)).eqTrans (snd_pair x.pos x.neg)))
    (congrAdd (.eqRefl _) ((congrFst (snd_pair X Y)).eqTrans (fst_pair y.pos y.neg)))
    (congrAdd (.eqRefl _) ((congrSnd (snd_pair X Y)).eqTrans (snd_pair y.pos y.neg)))

private theorem translated_coordinate (x y w : ZT n) (j : PTm n)
    (hp : Γ ⊢[PRAAx] w.pos ≐ x.pos+y.pos) (hn : Γ ⊢[PRAAx] w.neg ≐ x.neg+y.neg) :
    (Γ ⊢[PRAAx] (x+ZT.ofNat (one+j)*y).pos ≐ (w+ZT.ofNat j*y).pos) ∧
    (Γ ⊢[PRAAx] (x+ZT.ofNat (one+j)*y).neg ≐ (w+ZT.ofNat j*y).neg) := by
  constructor
  · change Γ ⊢[PRAAx] x.pos+((one+j)*y.pos+zero*y.neg) ≐ w.pos+(j*y.pos+zero*y.neg)
    exact (show Γ ⊢[PRAAx] x.pos+((one+j)*y.pos+zero*y.neg) ≐
      (x.pos+y.pos)+(j*y.pos+zero*y.neg) by ipra_ring).eqTrans (congrAdd hp.eqSymm (.eqRefl _))
  · change Γ ⊢[PRAAx] x.neg+((one+j)*y.neg+zero*y.pos) ≐ w.neg+(j*y.neg+zero*y.pos)
    exact (show Γ ⊢[PRAAx] x.neg+((one+j)*y.neg+zero*y.pos) ≐
      (x.neg+y.neg)+(j*y.neg+zero*y.pos) by ipra_ring).eqTrans (congrAdd hn.eqSymm (.eqRefl _))

theorem native_shift (z h j : PTm n) :
    Γ ⊢[PRAAx] add z (scale (one+j) h) ≐ add (add z h) (scale j h) := by
  let x := re z+re h
  let y := im z+im h
  let X := pairT x.pos x.neg
  let Y := pairT y.pos y.neg
  have real := translated_coordinate (Γ := Γ) (re z) (re h) (re (add z h)) j
    ((congrFst (fst_pair X Y)).eqTrans (fst_pair x.pos x.neg))
    ((congrSnd (fst_pair X Y)).eqTrans (snd_pair x.pos x.neg))
  have imag := translated_coordinate (Γ := Γ) (im z) (im h) (im (add z h)) j
    ((congrFst (snd_pair X Y)).eqTrans (fst_pair y.pos y.neg))
    ((congrSnd (snd_pair X Y)).eqTrans (snd_pair y.pos y.neg))
  exact (add_scaled z h (one+j)).eqTrans
    ((code_congr _ _ _ _ real.1 real.2 imag.1 imag.2).eqTrans (add_scaled (add z h) h j).eqSymm)

private theorem sequence_equal_from_entries (A C : PTm 2) (N x y : PTm n)
    (h : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      entry (Syn.shift (sequence A N x)) (var 0) ≐ entry (Syn.shift (sequence C N y)) (var 0)) :
    Γ ⊢[PRAAx] sequence A N x ≐ sequence C N y := by
  have atIndex : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      entry (sequence A (Syn.shift N) (Syn.shift x)) (var 0) ≐
        entry (sequence C (Syn.shift N) (Syn.shift y)) (var 0) := by simpa [Syn.shift] using h
  exact sequence_equal A C N x y (.allI (.impI
    ((sequence_decode A Prf.hyp0).eqSymm.eqTrans (atIndex.eqTrans (sequence_decode C Prf.hyp0)))))

theorem first_window (t z h R B e : PTm n) :
    Γ ⊢[PRAAx] slice (cofinalGrid t z h R B (succ e)) zero (succ e) ≐ cofinalGrid t z h R B e := by
  apply sequence_equal_from_entries
  let s (a : PTm n) := Syn.shift a
  let j : PTm (n+1) := var 0
  let Δ := lt j (succ (s e)) :: Γ.map Fm.shift
  let W := cofinalGrid (s t) (s z) (s h) (s R) (s B) (succ (s e))
  have hj : Δ ⊢[PRAAx] lt j (succ (s e)) := Prf.hyp0
  have long := lt_of_lt_of_le hj (le_succ_self (succ (s e)))
  have small := (slice_at W zero (succ (s e)) j hj).eqTrans (entry_congr (.eqRefl W) (zero_add j))
  have right := cofinal_at (s t) (s z) (s h) (s R) (s B) (s e) j hj
  have left := cofinal_at (s t) (s z) (s h) (s R) (s B) (succ (s e)) j long
  change Δ ⊢[PRAAx] entry (s (slice (cofinalGrid t z h R B (succ e)) zero (succ e))) j ≐
    entry (s (cofinalGrid t z h R B e)) j
  simpa [s,j,Δ,W,Syn.shift] using small.eqTrans (left.eqTrans right.eqSymm)

theorem next_window (t z h R B e : PTm n) :
    Γ ⊢[PRAAx] slice (cofinalGrid t z h R B (succ e)) one (succ e) ≐ cofinalGrid t (add z h) h R B e := by
  apply sequence_equal_from_entries
  let s (a : PTm n) := Syn.shift a
  let j : PTm (n+1) := var 0
  let Δ := lt j (succ (s e)) :: Γ.map Fm.shift
  let W := cofinalGrid (s t) (s z) (s h) (s R) (s B) (succ (s e))
  have hj : Δ ⊢[PRAAx] lt j (succ (s e)) := Prf.hyp0
  have long : Δ ⊢[PRAAx] lt (one+j) (succ (succ (s e))) :=
    le_congr (by ipra_ring) (.eqRefl _) ((succ_monus_succ _ _).eqTrans hj)
  have left := (slice_at W one (succ (s e)) j hj).eqTrans
    (cofinal_at (s t) (s z) (s h) (s R) (s B) (succ (s e)) (one+j) long)
  have right := cofinal_at (s t) (add (s z) (s h)) (s h) (s R) (s B) (s e) j hj
  have middle : Δ ⊢[PRAAx] ap2 GaussianBarnesCanonicalValue.nameF (s t) (cofinalData (s z) (s h) (s R) (s B) (one+j)) ≐
      ap2 GaussianBarnesCanonicalValue.nameF (s t) (cofinalData (add (s z) (s h)) (s h) (s R) (s B) j) := by
    ipra_congr (ap2 GaussianBarnesCanonicalValue.nameF (var 0)
      (GaussianBarnesCanonicalValue.data (var 1) (var 2) (var 3)) : PTm 4)
      with [.eqRefl _, native_shift (s z) (s h) j, .eqRefl _, .eqRefl _] using [cofinalData]
  change Δ ⊢[PRAAx] entry (s (slice (cofinalGrid t z h R B (succ e)) one (succ e))) j ≐
    entry (s (cofinalGrid t (add z h) h R B e)) j
  simpa [s,j,Δ,W,Syn.shift,one] using left.eqTrans (middle.eqTrans right.eqSymm)

theorem actual_Barnes_cofinal_grid_windows_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let t := var 0
       let z := var 1
       let h := var 2
       let R := var 3
       let B := var 4
       let e := var 5
       let V := cofinalGrid t z h R B (succ e)
       (slice V zero (succ e) ≐ cofinalGrid t z h R B e) ⋏
         (slice V one (succ e) ≐ cofinalGrid t (add z h) h R B e)) :=
  closeUniv 6 (.andI (first_window _ _ _ _ _ _) (next_window _ _ _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorGridWindows
