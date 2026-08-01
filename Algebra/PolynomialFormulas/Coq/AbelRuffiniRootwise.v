From mathcomp Require Import all_ssreflect all_algebra all_field.
From Abel Require Import abel.
From PolynomialFormulas Require Import AbelRuffini.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Notation ratrC := (@ratr algC).

Module PolynomialFormulasAbelRuffiniRootwise.

Import LeanProofs.PolynomialFormulasAbelRuffini.

(** Values represented by Abel's radical-expression language are stable under
    automorphisms of the algebraic closure that fix the rationals.  The root
    case may change the chosen root by a root of unity; [algterm] contains
    primitive roots of unity precisely so that the conjugate is representable
    as well. *)
Lemma algterm_eval_aut (nu : {rmorphism algC -> algC}) (f : algterm rat) :
  exists g : algterm rat, algT_eval ratrC g = nu (algT_eval ratrC f).
Proof.
elim: f => [q|c|u f [g gf]|b f1 [g1 g1f1] f2 [g2 g2f2]] /=.
- exists (Base q) => /=.
  by rewrite fmorph_rat.
- case: c => [| |n] /=.
  + by exists (@Const rat Zero); rewrite rmorph0.
  + by exists (@Const rat One); rewrite rmorph1.
  + have nu_root : (nu (prim1root_ n.+1)) ^+ n.+1 = 1.
      by rewrite -rmorphXn (prim_expr_order (prim1rootP (ltn0Sn n))) rmorph1.
    have [i nu_prim] := prim_rootP (prim1rootP (ltn0Sn n)) nu_root.
    exists (UnOp (Exp i) (@Const rat (URoot n))) => /=.
    exact: esym nu_prim.
- case: u => [| |m|m] /=.
  + exists (UnOp Opp g) => /=.
    by rewrite gf rmorphN.
  + exists (UnOp Inv g) => /=.
    by rewrite gf fmorphV.
  + exists (UnOp (Exp m) g) => /=.
    by rewrite gf rmorphXn.
  + pose v := m.+1.-root (algT_eval ratrC g).
    have nu_f_root :
        root ('X ^+ m.+1 - (v ^+ m.+1)%:P)
             (nu (m.+1.-root (algT_eval ratrC f))).
      apply/rootP.
      rewrite !hornerE ?hornerXn -rmorphXn rootCK //.
      rewrite /v (rootCK (ltn0Sn m)).
      by rewrite gf subrr.
    move: nu_f_root.
    have /Xn_sub_xnE -> // := prim1rootP (ltn0Sn m).
    rewrite /root horner_prod prodf_seq_eq0 /= => /hasP [i _].
    rewrite hornerXsubC subr_eq0 => /eqP nu_f.
    exists (BinOp Mul (UnOp (Root m) g)
                      (UnOp (Exp i) (@Const rat (URoot m)))) => /=.
    exact: esym nu_f.
- case: b => /=.
  + exists (BinOp Add g1 g2) => /=.
    by rewrite g1f1 g2f2 rmorphD.
  + exists (BinOp Mul g1 g2) => /=.
    by rewrite g1f1 g2f2 rmorphM.
Qed.

(** The concrete complex root list is exactly the root set of the quintic. *)
Lemma quintic_root_mem_example_roots x :
    x \in root (map_poly ratrC quintic_counterexample) ->
    x \in example_roots.
Proof. by rewrite -root_prod_XsubC -ratr_example_poly. Qed.

(** Reordering the number-field roots by nonreal/real status loses no root. *)
Lemma numfield_root_mem_reordered z :
    z \in numfield_roots poly_example ->
    z \in [seq u <- numfield_roots poly_example |
              numfield_inC poly_example u \isn't Num.real] ++
          [seq u <- numfield_roots poly_example |
              numfield_inC poly_example u \is Num.real].
Proof.
move=> zroot; rewrite mem_cat !mem_filter zroot /=.
by case: (numfield_inC poly_example z \is Num.real).
Qed.

(** Any two complex roots of the explicit irreducible quintic are related by
    an automorphism of [algC].  MathComp's normal number field contains all of
    the roots; normality gives the internal automorphism, which then extends
    to the algebraic closure. *)
Lemma quintic_roots_conjugate x y :
    x \in root (map_poly ratrC quintic_counterexample) ->
    y \in root (map_poly ratrC quintic_counterexample) ->
  exists nu : {rmorphism algC -> algC}, nu x = y.
Proof.
move=> xroot yroot.
have xex := quintic_root_mem_example_roots xroot.
have yex := quintic_root_mem_example_roots yroot.
have [rx rxr Dx] := mapP xex.
have [ry ryr Dy] := mapP yex.
have rxrp := numfield_root_mem_reordered rxr.
have ryrp := numfield_root_mem_reordered ryr.
have mroot : root (minPoly 1 rx) ry.
  rewrite (eqp_root (PDTNRR.minPoly_rp irreducible_example rxrp)).
  by rewrite [root _ _](PDTNRR.root_p irreducible_example) ryrp.
have [phi _ Dphi] := normalField_root_minPoly
  (sub1v fullv) (normal_numfield poly_example) (memvf rx) mroot.
have [nu Dnu] := extend_algC_subfield_aut
  (numfield_inC poly_example) phi.
exists nu.
rewrite Dx Dy -Dnu /= Dphi.
by [].
Qed.

Definition has_radical_expression (x : algC) : Prop :=
  exists f : algterm rat, algT_eval ratrC f = x.

(** Every complex root of the explicit irreducible quintic, individually,
    has no expression by rational constants, field operations, roots of unity,
    and radicals. *)
Theorem quintic_root_has_no_radical_expression x :
    x \in root (map_poly ratrC quintic_counterexample) ->
  ~ has_radical_expression x.
Proof.
move=> px [f fx].
apply: quintic_no_radical_formula => y py.
have [nu nuxy] := quintic_roots_conjugate px py.
have [g gnu] := algterm_eval_aut nu f.
exists g.
by rewrite gnu fx nuxy.
Qed.

Theorem quintic_every_root_has_no_radical_expression :
  {in root (map_poly ratrC quintic_counterexample),
    forall x, ~ has_radical_expression x}.
Proof. exact: quintic_root_has_no_radical_expression. Qed.

End PolynomialFormulasAbelRuffiniRootwise.
