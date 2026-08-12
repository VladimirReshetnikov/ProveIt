From mathcomp Require Import
  all_ssreflect all_fingroup all_solvable all_algebra all_field.
From Abel Require Import various map_gal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A generator-producing form of the cyclic Kummer argument.

    MathComp proves Hilbert's theorem 90, and MathComp-Abel uses it to show
    that a cyclic extension containing the required roots of unity is a
    radical extension.  For Lazard's radical-count statement we need the
    stronger, explicit output of that proof: one element whose [n]-th power
    lies in the base field and which generates the whole extension.

    This file spells out that construction.  In particular, no numerical
    degree hypothesis is reinterpreted as a radical presentation. *)
Module PolynomialFormulasLazardCyclicKummerGenerator.

Import GRing.Theory.
Local Open Scope ring_scope.

Section KummerGenerator.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Implicit Types (E F : {subfield L}) (w : L) (n : nat).

(** If [F/E] is cyclic Galois of degree [n] and [E] contains a primitive
    [n]-th root of unity, then a genuine Kummer generator exists in the
    common ambient field. *)
Lemma cyclic_kummer_generator w E F (n := \dim_E F) :
    n.-primitive_root w -> w \in E -> galois E F ->
  cyclic 'Gal(F / E) ->
  exists x : L,
    [/\ x \in F, x != 0, x ^+ n \in E & F = <<E; x>>%AS].
Proof.
set G := (X in cyclic X) => w_root wE galois_EF /cyclicP[g GE].
have EF := galois_subW galois_EF.
have n_gt0 : (n > 0)%N by rewrite /n -dim_aspaceOver ?adim_gt0.
have Gg : generator G g by rewrite GE generator_cycle.
have gG : g \in G by rewrite GE cycle_id.
have HT90g := Hilbert's_theorem_90 Gg (subvP EF _ wE).
have /eqP/HT90g[x [xF xN0]] : galNorm E F w = 1.
  rewrite /galNorm; under eq_bigr => g' g'G.
    rewrite (fixed_gal EF g'G) //.
  over.
  by rewrite prodr_const -galois_dim // (prim_expr_order w_root).
have gxN0 : g x != 0 by rewrite fmorph_eq0.
have wN0 : w != 0 by rewrite (primitive_root_eq0 w_root) -lt0n.
move=> /(canLR (mulfVK gxN0))/(canRL (mulKf wN0)) gx.
have gXx i : (g ^+ i)%g x = w ^- i * x.
  elim: i => [|i IHi].
    by rewrite expg0 expr0 invr1 mul1r gal_id.
  rewrite expgSr exprSr invfM galM // IHi rmorphM /= gx mulrA.
  by rewrite (fixed_gal EF gG) ?rpredV ?rpredX.
have xpowE : x ^+ n \in E.
  rewrite -(galois_fixedField galois_EF) -/G GE.
  apply/fixedFieldP; first by rewrite rpredX.
  move=> _ /cycleP[i ->]; rewrite rmorphXn /= gXx exprMn exprVn exprAC.
  by rewrite (prim_expr_order w_root) // expr1n invr1 mul1r.
have ExF : (<<E; x>> <= F)%VS by exact/FadjoinP.
have Fx : F = <<E; x>>%AS.
  apply/val_inj/eqP => /=.
  have -> : F = fixedField (1%g : {set gal_of F}) :> {vspace L}.
    by apply/esym/eqP; rewrite -galois_eq ?galvv ?galois_refl //.
  rewrite -galois_eq; last by apply: galoisS galois_EF; rewrite subv_adjoin.
  rewrite -subG1; apply/subsetP => g' g'G'.
  have /cycleP[i g'E] : g' \in <[g]>%g.
    rewrite -GE gal_kHom //; apply/kAHomP => y yE.
    by rewrite (fixed_gal _ g'G') ?subvP_adjoin.
  rewrite g'E in g'G' *.
  have : (g ^+ i)%g x = x.
    by rewrite (fixed_gal _ g'G') ?memv_adjoin.
  rewrite gXx => /(canRL (mulfK xN0))/eqP; rewrite divff // invr_eq1.
  rewrite -(prim_order_dvd w_root) => dvdni.
  have /exponentP-> // : (exponent G %| i)%N.
  by rewrite GE exponent_cycle orderE -GE -galois_dim.
by exists x; split.
Qed.

Print Assumptions cyclic_kummer_generator.

End KummerGenerator.

End PolynomialFormulasLazardCyclicKummerGenerator.
