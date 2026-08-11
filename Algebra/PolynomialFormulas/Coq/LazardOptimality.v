From mathcomp Require Import all_ssreflect all_fingroup all_algebra falgebra fieldext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Extension-theoretic foundations and the root-of-unity lower bound used
    in Lazard's optimality theorems. *)
Module PolynomialFormulasLazardOptimality.

Import GRing.Theory.
Local Open Scope ring_scope.

Section RadicalExtensions.

Variables (F0 : fieldType) (L : fieldExtType F0).
Implicit Types (K E M : {subfield L}).

(** Lazard's "prime power" means a power with prime exponent: [a ^+ p]
    for a prime [p], not an exponent of the form [p ^ k]. *)
Definition lazard_prime_exponent (p : nat) : Prop := prime p.

(** Audit note on the proof of Lazard's Theorem 3.  The literal condition
    [a ^+ p \in K] below only says that the minimal polynomial of [a] over
    [K] divides [X^p - a^p]; it does not make that minimal polynomial have
    degree [p].  For example, a primitive eleventh root of unity satisfies
    [a ^+ 11 = 1] over the rationals, while its degree is ten.  Consequently
    the inference in the paper from a degree divisible by five to "[p = 5]
    and the simple step has degree five" is not used here.  An unconditional
    formalization of that inference would need an additional prime-degree or
    irreducibility hypothesis on each simple radical step. *)
(** One simple radical adjunction in a common ambient field. *)
Definition simple_radical_step (K E : {subfield L}) : Prop :=
  exists (a : L) (p : nat),
    lazard_prime_exponent p /\ a ^+ p \in K /\
      (E : {vspace L}) = agenv ((K : {vspace L}) + <[a]>)%VS.

Lemma simple_radical_step_sub K E :
  simple_radical_step K E -> (K <= E)%VS.
Proof.
move=> [a [n [hn [han ->]]]].
exact: subv_adjoin.
Qed.

(** A finite chain of simple radical adjunctions. *)
Inductive radical_extension : {subfield L} -> {subfield L} -> Prop :=
| RadicalExtensionRefl K : radical_extension K K
| RadicalExtensionStep K E M :
    radical_extension K E ->
    simple_radical_step E M ->
    radical_extension K M.

Lemma radical_extension_sub K E :
  radical_extension K E -> (K <= E)%VS.
Proof.
move=> h; elim: h => [K0 | K0 E0 M0 hKE ih hEM].
- exact: subvv.
- exact: subv_trans ih (simple_radical_step_sub hEM).
Qed.

Lemma radical_extension_trans K E M :
  radical_extension K E -> radical_extension E M ->
  radical_extension K M.
Proof.
move=> hKE hEM; elim: hEM hKE => [E0 | E0 N P hEN ih hNP] hKE.
- exact: hKE.
- exact: RadicalExtensionStep (ih hKE) hNP.
Qed.

(** Literal leastness among radical extensions containing a specified set. *)
Record least_radical_extension_containing
    (K E : {subfield L}) (S : L -> Prop) : Prop := {
  least_radical_is_radical : radical_extension K E;
  least_radical_contains : forall x, S x -> x \in E;
  least_radical_least : forall M : {subfield L},
    radical_extension K M ->
    (forall x, S x -> x \in M) ->
    (E <= M)%VS
}.

Lemma least_radical_extension_unique K E M S :
  least_radical_extension_containing K E S ->
  least_radical_extension_containing K M S -> E = M.
Proof.
move=> hE hM; apply: val_inj; apply: subv_anti; apply/andP; split.
- exact: (least_radical_least hE
    (least_radical_is_radical hM) (least_radical_contains hM)).
- exact: (least_radical_least hM
    (least_radical_is_radical hE) (least_radical_contains hE)).
Qed.

(** A reusable refutation principle for a claimed least radical field.  If
    one competing radical field contains all specified roots but omits an
    element of the claimed field, literal leastness is impossible.  The
    Lean development instantiates this with the cyclic quintic inside the
    eleventh cyclotomic field and the omitted primitive fifth root. *)
Lemma not_least_radical_extension_of_missing_element K E M S (z : L) :
  radical_extension K M ->
  (forall x, S x -> x \in M) ->
  z \in E -> z \notin M ->
  ~ least_radical_extension_containing K E S.
Proof.
move=> hKM hSM hzE hzM hleast.
have hzM' : z \in M :=
  subvP (least_radical_least hleast hKM hSM) z hzE.
by move: hzM; rewrite hzM'.
Qed.

(** The corresponding direct refutation of an unconditional
    root-of-unity-forcing premise. *)
Lemma radicality_does_not_force_missing_element K M S (z : L) :
  radical_extension K M ->
  (forall x, S x -> x \in M) -> z \notin M ->
  ~ (forall N : {subfield L}, radical_extension K N ->
      (forall x, S x -> x \in N) -> z \in N).
Proof.
move=> hKM hSM hzM hforced.
have hzM' : z \in M := hforced M hKM hSM.
by move: hzM; rewrite hzM'.
Qed.

(** The missing arithmetic hypothesis in the printed proof of Theorem 3:
    every simple step contributes its prime exponent as its *actual* degree,
    so the total degree is their product.  Literal [simple_radical_step]
    alone does not imply this record. *)
Record prime_degree_tower_profile := PrimeDegreeTowerProfile {
  tower_total_degree : nat;
  tower_step_exponents : seq nat;
  tower_step_prime : all prime tower_step_exponents;
  tower_degree_product :
    tower_total_degree = \prod_(p <- tower_step_exponents) p
}.

Lemma five_mem_prime_steps_of_dvd_product (steps : seq nat) :
  all prime steps ->
  (5 %| \prod_(p <- steps) p)%N -> 5 \in steps.
Proof.
have h5 : prime 5 by [].
elim: steps => [|p ps ih] /=.
- by rewrite big_nil dvdn1.
- move=> /andP [hp hps].
  rewrite big_cons Euclid_dvdM // => /orP [h5p | h5ps].
  + rewrite in_cons; apply/orP; left.
    by move: h5p; rewrite dvdn_prime2.
  + rewrite in_cons; apply/orP; right.
    exact: ih hps h5ps.
Qed.

(** With that strengthened profile, divisibility by five really does force
    a fifth-root step. *)
Lemma prime_degree_tower_has_fifth_step
    (T : prime_degree_tower_profile) :
  (5 %| tower_total_degree T)%N -> 5 \in tower_step_exponents T.
Proof.
rewrite (tower_degree_product T).
exact: five_mem_prime_steps_of_dvd_product (tower_step_prime T).
Qed.

End RadicalExtensions.

Section RootOfUnityLowerBound.

Variables (F0 : fieldType) (L : fieldExtType F0).
Implicit Types (K : {subfield L}) (a z y : L).

(** Two nonzero members of one multiplicative orbit reveal their ratio. *)
Lemma ratio_mem_of_mem_mul K a z :
  a != 0 -> a \in K -> z * a \in K -> z \in K.
Proof.
move=> ha hKa hKza.
have hdiv : z * a / a \in K by exact: rpred_div hKza hKa.
by rewrite (mulfK ha z) in hdiv.
Qed.

(** A field containing all roots of a nonzero pure-power equation contains
    every corresponding root of unity. *)
Lemma root_of_unity_mem_of_all_power_roots K n y a z :
  a != 0 -> a ^+ n = y -> z ^+ n = 1 ->
  (forall b : L, b ^+ n = y -> b \in K) -> z \in K.
Proof.
move=> ha han hzn hall.
apply: (ratio_mem_of_mem_mul ha (hall a han)).
apply: hall.
by rewrite exprMn hzn han mul1r.
Qed.

(** Fifth-root specialization used by Lazard's all-roots theorem. *)
Lemma fifth_root_of_unity_mem_of_all_quintic_roots K y a z :
  a != 0 -> a ^+ 5 = y -> z ^+ 5 = 1 ->
  (forall b : L, b ^+ 5 = y -> b \in K) -> z \in K.
Proof.
exact: root_of_unity_mem_of_all_power_roots.
Qed.

End RootOfUnityLowerBound.

Print Assumptions simple_radical_step_sub.
Print Assumptions radical_extension_sub.
Print Assumptions radical_extension_trans.
Print Assumptions least_radical_extension_unique.
Print Assumptions not_least_radical_extension_of_missing_element.
Print Assumptions radicality_does_not_force_missing_element.
Print Assumptions five_mem_prime_steps_of_dvd_product.
Print Assumptions prime_degree_tower_has_fifth_step.
Print Assumptions ratio_mem_of_mem_mul.
Print Assumptions root_of_unity_mem_of_all_power_roots.
Print Assumptions fifth_root_of_unity_mem_of_all_quintic_roots.

End PolynomialFormulasLazardOptimality.
