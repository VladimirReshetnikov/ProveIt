(** Compatibility facade for ZF.L1_LProp. *)
From ZF Require Import Logic L1_LDef.
From K215Common Require Import PropositionalCore.
Module StandardBasis <: PropositionalBasis.
  Definition Formula := wff.
  Definition Imp := Wim.
  Definition Neg := Wn.
  Definition Pr := lprov.
  Definition mp := LDET.
  Definition b1 := LB1.
  Definition b2 := LB2.
  Definition b3 := LB3.
End StandardBasis.
Include PropositionalRules StandardBasis.
