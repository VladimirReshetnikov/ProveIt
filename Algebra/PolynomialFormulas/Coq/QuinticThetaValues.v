From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable.
From PolynomialFormulas Require Import QuinticF20Data QuinticThetaOrbit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Generic evaluation of the six scalar Frobenius--Dummit theta values.
    This file deliberately stops before choosing a splitting field or
    computing the symmetric coefficient formulas: it is only the algebraic
    value layer shared by those later arguments. *)
Module PolynomialFormulasQuinticThetaValues.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasQuinticThetaOrbit.

Local Open Scope ring_scope.
Local Open Scope group_scope.

Section Values.

Variable R : comRingType.

(** Evaluation of one five-variable exponent monomial. *)
Definition quintic_monomial_value
    (roots : 5.-tuple R) (d : quintic_exponent) : R :=
  \prod_(i : 'I_5) (tnth roots i) ^+ (tnth d i).

(** The theta polynomial represented by an arbitrary sequence of exponent
    rows.  In particular, duplicate rows contribute with multiplicity. *)
Definition quintic_table_value
    (roots : 5.-tuple R) (table : seq quintic_exponent) : R :=
  \sum_(d <- table) quintic_monomial_value roots d.

Lemma quintic_table_value_perm roots table1 table2 :
  perm_eq table1 table2 ->
  quintic_table_value roots table1 = quintic_table_value roots table2.
Proof. exact: perm_big. Qed.

(** Relabel a root tuple by a permutation.  With MathComp's permutation
    multiplication this is a right action: multiplication is read in the
    same order as the anti-homomorphic exponent identity
    [act_exponent_mul]. *)
Definition permute_quintic_roots (s : S5) (roots : 5.-tuple R) :
    5.-tuple R :=
  [tuple tnth roots (s i) | i < 5].

Lemma tnth_permute_quintic_roots s roots i :
  tnth (permute_quintic_roots s roots) i = tnth roots (s i).
Proof. by rewrite /permute_quintic_roots tnth_mktuple. Qed.

Lemma permute_quintic_roots_one roots :
  permute_quintic_roots 1 roots = roots.
Proof.
apply: eq_from_tnth=> i.
by rewrite tnth_permute_quintic_roots perm1.
Qed.

Lemma permute_quintic_roots_mul s t roots :
  permute_quintic_roots (s * t) roots =
    permute_quintic_roots s (permute_quintic_roots t roots).
Proof.
apply: eq_from_tnth=> i.
by rewrite !tnth_permute_quintic_roots permM.
Qed.

Lemma quintic_monomial_value_permute roots s d :
  quintic_monomial_value (permute_quintic_roots s roots) d =
    quintic_monomial_value roots (act_exponent s d).
Proof.
rewrite /quintic_monomial_value.
rewrite (reindex_inj (@perm_inj _ s^-1)) /=.
apply: eq_bigr=> i _.
by rewrite tnth_permute_quintic_roots permKV /act_exponent tnth_mktuple.
Qed.

Lemma quintic_table_value_permute roots s table :
  quintic_table_value (permute_quintic_roots s roots) table =
    quintic_table_value roots (map (act_exponent s) table).
Proof.
rewrite /quintic_table_value big_map.
apply: eq_bigr=> d _.
exact: quintic_monomial_value_permute.
Qed.

Lemma quintic_table_value_action_mul roots s t table :
  quintic_table_value roots (map (act_exponent (s * t)) table) =
  quintic_table_value roots
    (map (act_exponent t) (map (act_exponent s) table)).
Proof.
rewrite -!quintic_table_value_permute.
by rewrite permute_quintic_roots_mul.
Qed.

(** The six values use the inverse representatives selected in
    [QuinticThetaOrbit].  This is the orientation compatible with
    [theta_table_orbit_exhaustive]. *)
Definition quintic_theta_value (roots : 5.-tuple R) (i : 'I_6) : R :=
  quintic_table_value roots
    (theta_table_image ((representative i)^-1)).

Definition quintic_theta_values (roots : 5.-tuple R) : 6.-tuple R :=
  [tuple quintic_theta_value roots i | i < 6].

Lemma tnth_quintic_theta_values roots i :
  tnth (quintic_theta_values roots) i = quintic_theta_value roots i.
Proof. by rewrite /quintic_theta_values tnth_mktuple. Qed.

(** Acting on the roots appends [g] on the right of the current exponent
    table.  The inverse representative chosen for that orbit is therefore
    the one attached to [(representative i)^-1 * g]. *)
Definition quintic_theta_index_action (g : S5) (i : 'I_6) : 'I_6 :=
  inverse_representative_index ((representative i)^-1 * g).

Lemma inverse_representative_theta_orbits_perm_injective i j :
  perm_eq
      (theta_table_image ((representative i)^-1))
      (theta_table_image ((representative j)^-1)) ->
  i = j.
Proof.
move=> hij.
have hdistinct :=
  forallP (forallP inverse_representative_theta_orbits_distinct i) j.
have hijb : i == j.
  by move: hdistinct; rewrite hij /=.
exact/eqP.
Qed.

Lemma quintic_theta_index_action_one i :
  quintic_theta_index_action 1 i = i.
Proof.
apply: inverse_representative_theta_orbits_perm_injective.
rewrite /quintic_theta_index_action mulg1.
by rewrite perm_sym; exact: theta_table_orbit_exhaustive.
Qed.

(** This is the explicit anti-homomorphic orientation: exponent actions
    compose as [act_exponent t \o act_exponent s], so the induced index for
    [s * t] is obtained by first acting by [s], then by [t]. *)
Lemma quintic_theta_index_action_mul s t i :
  quintic_theta_index_action (s * t) i =
    quintic_theta_index_action t (quintic_theta_index_action s i).
Proof.
pose si := (representative i)^-1.
pose idxs := quintic_theta_index_action s i.
have hs : perm_eq (theta_table_image (si * s))
    (theta_table_image ((representative idxs)^-1)).
  exact: theta_table_orbit_exhaustive.
have hst := perm_map (act_exponent t) hs.
rewrite -!theta_table_image_mul in hst.
have hleft : perm_eq (theta_table_image (si * (s * t)))
    (theta_table_image
      ((representative (quintic_theta_index_action (s * t) i))^-1)).
  exact: theta_table_orbit_exhaustive.
have hright :
    perm_eq (theta_table_image ((representative idxs)^-1 * t))
      (theta_table_image
        ((representative (quintic_theta_index_action t idxs))^-1)).
  exact: theta_table_orbit_exhaustive.
apply: inverse_representative_theta_orbits_perm_injective.
have hmid :
    perm_eq (theta_table_image (si * (s * t)))
      (theta_table_image ((representative idxs)^-1 * t)).
  by move: hst; rewrite mulgA.
have hleft' :
    perm_eq
      (theta_table_image
        ((representative (quintic_theta_index_action (s * t) i))^-1))
      (theta_table_image (si * (s * t))).
  by move: hleft; rewrite perm_sym.
exact: perm_trans hleft' (perm_trans hmid hright).
Qed.

Lemma quintic_theta_index_action_injective g :
  injective (quintic_theta_index_action g).
Proof.
move=> i j hij.
have h := congr1 (quintic_theta_index_action g^-1) hij.
move: h.
rewrite -!quintic_theta_index_action_mul mulgV
  !quintic_theta_index_action_one.
by [].
Qed.

Lemma quintic_theta_index_action_bijective g :
  bijective (quintic_theta_index_action g).
Proof.
apply: (@injF_bij 'I_6 (quintic_theta_index_action g)).
exact: quintic_theta_index_action_injective.
Qed.

Lemma quintic_theta_value_permute roots g i :
  quintic_theta_value (permute_quintic_roots g roots) i =
    quintic_theta_value roots (quintic_theta_index_action g i).
Proof.
rewrite /quintic_theta_value quintic_table_value_permute.
rewrite -theta_table_image_mul.
apply: quintic_table_value_perm.
exact: theta_table_orbit_exhaustive.
Qed.

(** The scalar resolvent is directly the monic product over the six values. *)
Definition quintic_scalar_resolvent (roots : 5.-tuple R) : {poly R} :=
  \prod_(a <- quintic_theta_values roots) ('X - a%:P).

Definition quintic_scalar_resolvent_by_index
    (roots : 5.-tuple R) : {poly R} :=
  \prod_(i : 'I_6) ('X - (quintic_theta_value roots i)%:P).

Lemma quintic_scalar_resolvent_index_product roots :
  quintic_scalar_resolvent roots =
    quintic_scalar_resolvent_by_index roots.
Proof.
rewrite /quintic_scalar_resolvent /quintic_scalar_resolvent_by_index
  big_tuple.
by apply: eq_bigr=> i _; rewrite tnth_quintic_theta_values.
Qed.

Lemma quintic_scalar_resolvent_permute roots g :
  quintic_scalar_resolvent (permute_quintic_roots g roots) =
    quintic_scalar_resolvent roots.
Proof.
rewrite !quintic_scalar_resolvent_index_product.
rewrite /quintic_scalar_resolvent_by_index.
under [LHS]eq_bigr=> i _ do rewrite quintic_theta_value_permute.
rewrite [RHS](reindex_inj (@quintic_theta_index_action_injective g)).
by [].
Qed.

Lemma quintic_scalar_resolvent_monic roots :
  quintic_scalar_resolvent roots \is monic.
Proof. exact: monic_prod_XsubC. Qed.

Lemma size_quintic_scalar_resolvent roots :
  size (quintic_scalar_resolvent roots) = 7%N.
Proof.
by rewrite /quintic_scalar_resolvent size_prod_XsubC size_tuple.
Qed.

End Values.

Section RootCharacterization.

Variable R : idomainType.

Lemma quintic_scalar_resolvent_rootP (roots : 5.-tuple R) (x : R) :
  reflect (exists i : 'I_6, quintic_theta_value roots i = x)
    (root (quintic_scalar_resolvent roots) x).
Proof.
rewrite /quintic_scalar_resolvent root_prod_XsubC.
apply: (iffP idP).
- move=> /tnthP[i ->].
  by exists i; rewrite tnth_quintic_theta_values.
- move=> [i hix].
  apply/tnthP; exists i.
  by rewrite tnth_quintic_theta_values hix.
Qed.

Lemma quintic_scalar_resolvent_root_iff
    (roots : 5.-tuple R) (x : R) :
  root (quintic_scalar_resolvent roots) x <->
    exists i : 'I_6, quintic_theta_value roots i = x.
Proof.
split.
- exact: elimT (quintic_scalar_resolvent_rootP roots x).
- exact: introT (quintic_scalar_resolvent_rootP roots x).
Qed.

End RootCharacterization.

End PolynomialFormulasQuinticThetaValues.
