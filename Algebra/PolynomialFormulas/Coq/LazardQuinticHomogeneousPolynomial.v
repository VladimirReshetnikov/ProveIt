From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Executable four-variable homogeneous exponents.  The degree enumerator
    chooses the first three coordinates in nested bounded ranges and makes
    the fourth coordinate the remainder.  Thus it traverses weak
    compositions directly instead of scanning a four-dimensional cube. *)
Module PolynomialFormulasLazardQuinticHomogeneousPolynomial.

Definition HExponent := 4.-tuple nat.

Definition hexponent_zero : HExponent := [tuple 0%N | _ < 4].

Definition hexponent_single (j : 'I_4) : HExponent :=
  [tuple if i == j then 1%N else 0%N | i < 4].

Definition hexponent_add (a b : HExponent) : HExponent :=
  [tuple tnth a i + tnth b i | i < 4].

Definition hexponent_sub (a b : HExponent) : HExponent :=
  [tuple tnth a i - tnth b i | i < 4].

Definition hexponent_le (a b : HExponent) : bool :=
  [forall i : 'I_4, tnth a i <= tnth b i].

Definition hexponent_total (a : HExponent) : nat :=
  \sum_(i : 'I_4) tnth a i.

Definition degree_exponents (degree : nat) : seq HExponent :=
  flatten
    [seq flatten
      [seq
        [seq [tuple a; b; c; degree - a - b - c]
          | c <- iota 0 (degree - a - b).+1]
        | b <- iota 0 (degree - a).+1]
      | a <- iota 0 degree.+1].

Definition valid_splits (target : HExponent) (left_degree : nat) :
    seq HExponent :=
  [seq left <- degree_exponents left_degree | hexponent_le left target].

Lemma tnth_hexponent_zeroE (i : 'I_4) :
  tnth hexponent_zero i = 0%N.
Proof. by rewrite /hexponent_zero tnth_mktuple. Qed.

Lemma tnth_hexponent_singleE (i j : 'I_4) :
  tnth (hexponent_single j) i =
    if i == j then 1%N else 0%N.
Proof. by rewrite /hexponent_single tnth_mktuple. Qed.

Lemma tnth_hexponent_addE (a b : HExponent) (i : 'I_4) :
  tnth (hexponent_add a b) i = tnth a i + tnth b i.
Proof. by rewrite /hexponent_add tnth_mktuple. Qed.

Lemma tnth_hexponent_subE (a b : HExponent) (i : 'I_4) :
  tnth (hexponent_sub a b) i = tnth a i - tnth b i.
Proof. by rewrite /hexponent_sub tnth_mktuple. Qed.

Lemma hexponent_leP (a b : HExponent) :
  reflect (forall i : 'I_4, tnth a i <= tnth b i)
    (hexponent_le a b).
Proof. exact: (iffP forallP). Qed.

Lemma hexponent_total_zero :
  hexponent_total hexponent_zero = 0%N.
Proof.
rewrite /hexponent_total.
under eq_bigr do rewrite tnth_hexponent_zeroE.
by rewrite big1.
Qed.

Lemma hexponent_total_single (j : 'I_4) :
  hexponent_total (hexponent_single j) = 1%N.
Proof.
rewrite /hexponent_total (bigD1 j) //= tnth_hexponent_singleE eqxx.
rewrite big1 ?addn0 // => i hij.
by rewrite tnth_hexponent_singleE (negbTE hij).
Qed.

Lemma hexponent_total_add (a b : HExponent) :
  hexponent_total (hexponent_add a b) =
    hexponent_total a + hexponent_total b.
Proof.
rewrite /hexponent_total.
under [LHS] eq_bigr do rewrite tnth_hexponent_addE.
exact: big_split.
Qed.

Lemma hexponent_sub_addK (a b : HExponent) :
  hexponent_le a b ->
  hexponent_add a (hexponent_sub b a) = b.
Proof.
move/hexponent_leP=> hab; apply: eq_from_tnth=> i.
by rewrite tnth_hexponent_addE tnth_hexponent_subE subnKC //; exact: hab.
Qed.

Lemma hexponent_subK (a b : HExponent) :
  hexponent_le a b ->
  hexponent_add (hexponent_sub b a) a = b.
Proof.
move/hexponent_leP=> hab; apply: eq_from_tnth=> i.
by rewrite tnth_hexponent_addE tnth_hexponent_subE subnK //; exact: hab.
Qed.

Lemma hexponent_total_sub (a b : HExponent) :
  hexponent_le a b ->
  hexponent_total (hexponent_sub b a) =
    hexponent_total b - hexponent_total a.
Proof.
move=> hab.
have h := congr1 hexponent_total (hexponent_subK hab).
rewrite hexponent_total_add in h.
by rewrite -h addnK.
Qed.

(** A logical view of the three nested bounded loops.  Keeping this lemma
    separate lets later proofs reason about the enumerator without
    unfolding it, while the actual certificate evaluator still executes
    the compact weak-composition traversal above. *)
Lemma degree_exponentsP degree (e : HExponent) :
  reflect
    (exists a b c : nat,
      [&& a <= degree,
          b <= degree - a,
          c <= degree - a - b &
          e == [tuple a; b; c; degree - a - b - c]])
    (e \in degree_exponents degree).
Proof.
apply: (iffP flatten_mapP).
- move=> [a ha he].
  move/flatten_mapP: he=> [b hb he].
  move/mapP: he=> [c hc ->].
  exists a, b, c.
  move: ha hb hc; rewrite !mem_iota !add0n !ltnS !leq0n /=.
  by move=> -> -> ->; rewrite eqxx.
- move=> [a [b [c /and4P [ha hb hc /eqP ->]]]].
  exists a.
  - by rewrite mem_iota add0n ltnS leq0n.
  apply/flatten_mapP.
  exists b.
  - by rewrite mem_iota add0n ltnS leq0n.
  apply/mapP.
  exists c=> //.
  by rewrite mem_iota add0n ltnS leq0n.
Qed.

Lemma hexponent_total_tuple4 a b c d :
  hexponent_total [tuple a; b; c; d] = a + b + c + d.
Proof. by rewrite /hexponent_total !big_ord_recr big_ord0 /=. Qed.

Lemma hexponent_tuple4 (e : HExponent) :
  exists a b c d : nat, e = [tuple a; b; c; d].
Proof.
case/tupleP: e=> a e; case/tupleP: e=> b e.
case/tupleP: e=> c e; case/tupleP: e=> d e.
rewrite (tuple0 e).
by exists a, b, c, d.
Qed.

Lemma degree_exponents_total degree e :
  e \in degree_exponents degree -> hexponent_total e = degree.
Proof.
move/degree_exponentsP=> [a [b [c /and4P [ha hb hc /eqP ->]]]].
rewrite hexponent_total_tuple4.
by rewrite -!addnA (subnKC hc) (subnKC hb) (subnKC ha).
Qed.

Lemma degree_exponents_complete degree e :
  hexponent_total e = degree -> e \in degree_exponents degree.
Proof.
case: (hexponent_tuple4 e)=> a [b [c [d ->]]].
rewrite hexponent_total_tuple4=> htotal.
apply/degree_exponentsP.
exists a, b, c.
have hda : degree - a = b + (c + d).
  by rewrite -htotal -!addnA addKn.
have hdab : degree - a - b = c + d by rewrite hda addKn.
have ha : a <= degree.
  by rewrite -htotal -!addnA; exact: leq_addr.
have hb : b <= degree - a by rewrite hda; exact: leq_addr.
have hc : c <= degree - a - b by rewrite hdab; exact: leq_addr.
have hd : d = degree - a - b - c by rewrite hdab addKn.
by rewrite ha hb hc hd eqxx.
Qed.

Lemma tuple4_eq_coord0 (a b c d a' b' c' d' : nat) :
  [tuple a; b; c; d] = [tuple a'; b'; c'; d'] -> a = a'.
Proof.
move=> h.
have h0 := congr1 (fun e : HExponent => nth 0 e 0) h.
by move: h0; rewrite /=.
Qed.

Lemma tuple4_eq_coord1 (a b c d a' b' c' d' : nat) :
  [tuple a; b; c; d] = [tuple a'; b'; c'; d'] -> b = b'.
Proof.
move=> h.
have h1 := congr1 (fun e : HExponent => nth 0 e 1) h.
by move: h1; rewrite /=.
Qed.

Lemma tuple4_eq_coord2 (a b c d a' b' c' d' : nat) :
  [tuple a; b; c; d] = [tuple a'; b'; c'; d'] -> c = c'.
Proof.
move=> h.
have h2 := congr1 (fun e : HExponent => nth 0 e 2) h.
by move: h2; rewrite /=.
Qed.

Lemma degree_exponents_uniq degree : uniq (degree_exponents degree).
Proof.
have inner_uniq a :
    uniq (flatten
      [seq [seq [tuple a; b; c; degree - a - b - c]
              | c <- iota 0 (degree - a - b).+1]
        | b <- iota 0 (degree - a).+1]).
  apply/allpairs_uniq_dep.
  - exact: iota_uniq.
  - by move=> b _; exact: iota_uniq.
  - move=> [b c] [b' c'] _ _ /= he.
    have hb := tuple4_eq_coord1 he.
    have hc := tuple4_eq_coord2 he.
    by subst b'; subst c'.
rewrite /degree_exponents.
pose rows a := flatten
  [seq [seq [tuple a; b; c; degree - a - b - c]
          | c <- iota 0 (degree - a - b).+1]
    | b <- iota 0 (degree - a).+1].
change (uniq (flatten [seq rows a | a <- iota 0 degree.+1])).
have rows_allpairs :
    flatten [seq rows a | a <- iota 0 degree.+1] =
      [seq e | a <- iota 0 degree.+1, e <- rows a].
  elim: (iota 0 degree.+1)=> [|a s ih] //=.
  by rewrite map_id ih.
rewrite rows_allpairs.
apply/allpairs_uniq_dep.
- exact: iota_uniq.
- by move=> a _; exact: inner_uniq.
- move=> p q hp hq.
  move/allpairsPdep: hp=> [a [e [_ he_a ->]]].
  move/allpairsPdep: hq=> [a' [e' [_ he_a' ->]]].
  rewrite /rows in he_a he_a'.
  move/flatten_mapP: he_a=> [b _ /mapP [c _ ->]].
  move/flatten_mapP: he_a'=> [b' _ /mapP [c' _ ->]].
  move=> /= he.
  have ha := tuple4_eq_coord0 he.
  subst a'.
  apply/eqP; rewrite eq_Tagged; apply/eqP.
  exact: he.
Qed.

Lemma mem_degree_exponents degree e :
  (e \in degree_exponents degree) = (hexponent_total e == degree).
Proof.
apply/idP/eqP.
- exact: degree_exponents_total.
- exact: degree_exponents_complete.
Qed.

Lemma mem_valid_splits target left_degree left :
  (left \in valid_splits target left_degree) =
  (hexponent_total left == left_degree) && hexponent_le left target.
Proof. by rewrite /valid_splits mem_filter mem_degree_exponents andbC. Qed.

End PolynomialFormulasLazardQuinticHomogeneousPolynomial.
