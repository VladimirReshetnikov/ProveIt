From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data
  LazardQuinticRootProjections.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Cayley's invariant and Lazard's [i4].

    Section 6 defines [V] and [W] as the two cyclic quadratic orbit sums and
    states [(V-W)^2 = 4 i4 + p^2 + 12 r] for depressed roots.  We first prove
    the stronger identity with the missing [-4 e1 e3] term, then specialize
    it at [e1 = 0]. *)
Module PolynomialFormulasLazardQuinticCayleyTranslation.

Import GRing.Theory.
Module F20 := PolynomialFormulasQuinticF20Data.
Module RP := PolynomialFormulasLazardQuinticRootProjections.

Local Open Scope ring_scope.

Section CayleyTranslation.

Variable F : fieldType.

(** The cyclic nearest-neighbour quadratic sum [V]. *)
Definition lazard_root_cayley_V (roots : 5.-tuple F) : F :=
  tnth roots F20.o0 * tnth roots F20.o1 +
  tnth roots F20.o1 * tnth roots F20.o2 +
  tnth roots F20.o2 * tnth roots F20.o3 +
  tnth roots F20.o3 * tnth roots F20.o4 +
  tnth roots F20.o4 * tnth roots F20.o0.

(** The cyclic next-nearest-neighbour quadratic sum [W]. *)
Definition lazard_root_cayley_W (roots : 5.-tuple F) : F :=
  tnth roots F20.o0 * tnth roots F20.o2 +
  tnth roots F20.o1 * tnth roots F20.o3 +
  tnth roots F20.o2 * tnth roots F20.o4 +
  tnth roots F20.o3 * tnth roots F20.o0 +
  tnth roots F20.o4 * tnth roots F20.o1.

(** Cayley's root invariant [Theta = (V-W)^2]. *)
Definition lazard_root_cayley_theta (roots : 5.-tuple F) : F :=
  (lazard_root_cayley_V roots - lazard_root_cayley_W roots) ^+ 2.

(** The coefficient-side translate used by Lazard in Sections 6 and 7. *)
Definition lazard_cayley_theta
    (c : RP.LazardDepressedRootCoefficients F) (i4 : F) : F :=
  4%:R * i4 + RP.lazard_root_p c ^+ 2 + 12%:R * RP.lazard_root_r c.

(** Expose MathComp's packed operations to the standard kernel-producing
    [ring] tactic. *)
Let ring_carrier : Type := F.
Local Definition ring_zero : ring_carrier := @GRing.zero F.
Local Definition ring_one : ring_carrier := @GRing.one F.
Local Definition ring_add : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.add F.
Local Definition ring_mul : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.mul F.
Local Definition ring_sub : ring_carrier -> ring_carrier -> ring_carrier :=
  fun x y => x - y.
Local Definition ring_opp : ring_carrier -> ring_carrier := @GRing.opp F.
Local Definition ring_eq : ring_carrier -> ring_carrier -> Prop :=
  @eq ring_carrier.

Lemma ring_addE (x y : F) : x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma ring_mulE (x y : F) : x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma ring_subE (x y : F) : x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma ring_oppE (x : F) : - x = ring_opp x. Proof. reflexivity. Qed.
Lemma ring_zeroE : (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma ring_oneE : @GRing.one F = ring_one. Proof. reflexivity. Qed.

Lemma cayley_ring_theory :
  @ring_theory ring_carrier ring_zero ring_one ring_add ring_mul
    ring_sub ring_opp ring_eq.
Proof.
constructor; unfold ring_zero, ring_one, ring_add, ring_mul, ring_sub,
  ring_opp, ring_eq; intros.
- exact: add0r.
- exact: addrC.
- exact: addrA.
- exact: mul1r.
- exact: mulrC.
- exact: mulrA.
- exact: mulrDl.
- reflexivity.
- exact: addrN.
Qed.

Add Ring lazard_cayley_ring : cayley_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Lemma two_natrE : (2%:R : F) = 1 + 1.
Proof. exact: (@natrD F 1 1). Qed.

Lemma three_natrE : (3%:R : F) = 2%:R + 1.
Proof. exact: (@natrD F 2 1). Qed.

Lemma four_natrE : (4%:R : F) = 2%:R * 2%:R.
Proof. exact: (@natrM F 2 2). Qed.

Lemma twelve_natrE : (12%:R : F) = 4%:R * 3%:R.
Proof. exact: (@natrM F 4 3). Qed.

Lemma expr2E (x : F) : x ^+ 2 = x * x.
Proof. by rewrite expr2. Qed.

Lemma expr1E (x : F) : x ^+ 1 = x.
Proof. by rewrite expr1. Qed.

Ltac finish_cayley_ring :=
  repeat first
    [ rewrite twelve_natrE | rewrite four_natrE | rewrite three_natrE
    | rewrite two_natrE | rewrite expr2E | rewrite expr1E
    | rewrite ring_addE | rewrite ring_mulE | rewrite ring_subE
    | rewrite ring_oppE | rewrite ring_zeroE | rewrite ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

(** The unrestricted identity.  The correction term vanishes exactly in
    the depressed case used by the paper. *)
Theorem lazard_root_cayley_theta_elementaryE (roots : 5.-tuple F) :
  lazard_root_cayley_theta roots =
    4%:R * RP.lazard_root_i4 (RP.lazard_root_invariants roots) +
      RP.lazard_root_esymm2 roots ^+ 2 -
      4%:R * RP.lazard_root_esymm1 roots *
        RP.lazard_root_esymm3 roots +
      12%:R * RP.lazard_root_esymm4 roots.
Proof.
rewrite /lazard_root_cayley_theta /lazard_root_cayley_V
  /lazard_root_cayley_W /RP.lazard_root_invariants /=
  /RP.lazard_root_orbit_formula /RP.lazard_root_esymm1
  /RP.lazard_root_esymm2 /RP.lazard_root_esymm3
  /RP.lazard_root_esymm4.
finish_cayley_ring.
Qed.

(** Lazard's printed equation [Theta = 4 i4 + p^2 + 12 r]. *)
Theorem lazard_root_cayley_theta_depressedE (roots : 5.-tuple F)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  lazard_root_cayley_theta roots =
    lazard_cayley_theta (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_i4 (RP.lazard_root_invariants roots)).
Proof.
rewrite lazard_root_cayley_theta_elementaryE hsum mulr0 mul0r subr0.
by rewrite /lazard_cayley_theta /RP.lazard_depressed_of_roots /=.
Qed.

End CayleyTranslation.

Print Assumptions lazard_root_cayley_theta_elementaryE.
Print Assumptions lazard_root_cayley_theta_depressedE.

End PolynomialFormulasLazardQuinticCayleyTranslation.
