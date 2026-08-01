From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From PolynomialFormulas Require Import SexticSparsePolynomials.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Finite inclusion--exclusion for symmetric polynomials in six variables.
    Set partitions are represented by the unique regressive idempotent map
    sending every position to the least position in its block.  This gives a
    small transparent list of the 203 partitions and keeps the finite kernel
    computation independent of MathComp's much larger finite-set encodings. *)
Module PolynomialFormulasSexticPowerSumSymmetric.

Import PolynomialFormulasSexticSparsePolynomials.

Definition root_index := 'I_6.
Definition six_naturals : seq nat := iota 0 6.

Definition extend_regressive (s : seq nat) : seq (seq nat) :=
  [seq rcons s j | j <- iota 0 (size s).+1].

Definition regressive_step (prefixes : seq (seq nat)) : seq (seq nat) :=
  flatten [seq extend_regressive s | s <- prefixes].

Fixpoint regressive_lists_from
    (steps : nat) (prefixes : seq (seq nat)) : seq (seq nat) :=
  if steps is steps'.+1 then
    regressive_lists_from steps' (regressive_step prefixes)
  else prefixes.

Definition regressive_lists : seq (seq nat) :=
  regressive_lists_from 6 [:: [::]].

Definition partition_codeb (s : seq nat) : bool :=
  all (fun i => nth 0 s (nth 0 s i) == nth 0 s i) six_naturals.

Definition partition_codes : seq (seq nat) :=
  [seq s <- regressive_lists | partition_codeb s].

Definition block_size (s : seq nat) (j : nat) : nat :=
  count_mem j s.

Fixpoint transparent_factorial (n : nat) : nat :=
  if n is n'.+1 then n * transparent_factorial n' else 1%nat.

Definition block_mobius_size (n : nat) : Z :=
  if odd n.-1 then Z.opp (Z.of_nat (transparent_factorial n.-1))
  else Z.of_nat (transparent_factorial n.-1).

Definition partition_mobius (s : seq nat) : Z :=
  foldr Z.mul 1%Z
    (map (fun j => block_mobius_size (block_size s j))
      [seq j <- six_naturals | block_size s j != 0%nat]).

Definition code_refines_kernel (s f : seq nat) : bool :=
  all (fun i =>
    all (fun j =>
      (nth 0 s i == nth 0 s j) ==> (nth 0 f i == nth 0 f j))
      six_naturals)
    six_naturals.

Definition code_injectiveb (f : seq nat) : bool := uniq f.

Definition kernel_mobius_sum (f : seq nat) : Z :=
  foldr Z.add 0%Z
    (map partition_mobius
      [seq s <- partition_codes | code_refines_kernel s f]).

Definition partition_mobius_positive (s : seq nat) : nat :=
  Z.to_nat (partition_mobius s).

Definition partition_mobius_negative (s : seq nat) : nat :=
  Z.to_nat (Z.opp (partition_mobius s)).

Definition kernel_mobius_positive_sum (f : seq nat) : nat :=
  foldr addn 0
    (map partition_mobius_positive
      [seq s <- partition_codes | code_refines_kernel s f]).

Definition kernel_mobius_negative_sum (f : seq nat) : nat :=
  foldr addn 0
    (map partition_mobius_negative
      [seq s <- partition_codes | code_refines_kernel s f]).

Definition partition_count : nat := size partition_codes.

Definition partition_regressiveb (s : seq nat) : bool :=
  all (fun i => (nth 0 s i <= i)%nat) six_naturals.

(** Besides counting the partition table, we check once and transparently
    that every generated entry has the representation invariants used below.
    Keeping this as a Boolean certificate makes the later algebraic argument
    independent of the implementation details of [regressive_lists_from]. *)
Lemma partition_codes_well_formed :
  all (fun s =>
    (size s == 6) && partition_codeb s && partition_regressiveb s)
    partition_codes.
Proof. by vm_compute. Qed.

Lemma partition_code_size s : s \in partition_codes -> size s = 6.
Proof.
move=> hs.
move/allP: partition_codes_well_formed=> hwell.
move/andP: (hwell s hs)=> [/andP [/eqP hsize _] _].
exact hsize.
Qed.

Lemma partition_code_idempotent s :
  s \in partition_codes -> partition_codeb s.
Proof.
move=> hs.
move/allP: partition_codes_well_formed=> hwell.
move/andP: (hwell s hs)=> [/andP [_ hid] _].
exact hid.
Qed.

Lemma partition_code_regressive s i :
  s \in partition_codes -> (i < 6)%nat -> (nth 0 s i <= i)%nat.
Proof.
move=> hs hi.
move/allP: partition_codes_well_formed=> hwell.
move/andP: (hwell s hs)=> [_ hreg].
apply: (allP hreg i).
by rewrite /six_naturals mem_iota add0n hi.
Qed.

Lemma extend_regressive_mem (prefixes : seq (seq nat)) (s : seq nat) (j : nat) :
  s \in prefixes -> (j <= size s)%nat ->
  rcons s j \in regressive_step prefixes.
Proof.
move=> hs hj; apply/flattenP.
exists (extend_regressive s).
  by apply/mapP; exists s.
apply/mapP; exists j; last by [].
by rewrite mem_iota add0n ltnS.
Qed.

Arguments extend_regressive_mem {prefixes s j} _ _.

Lemma regressive_lists_complete s :
  size s = 6 ->
  (forall i, (i < 6)%nat -> (nth 0 s i <= i)%nat) ->
  s \in regressive_lists.
Proof.
move=> hs hreg.
pose R0 : seq (seq nat) := [:: [::]].
pose R1 := regressive_step R0.
pose R2 := regressive_step R1.
pose R3 := regressive_step R2.
pose R4 := regressive_step R3.
pose R5 := regressive_step R4.
pose R6 := regressive_step R5.
have hlt0 : (0 < size s)%nat by rewrite hs.
have hlt1 : (1 < size s)%nat by rewrite hs.
have hlt2 : (2 < size s)%nat by rewrite hs.
have hlt3 : (3 < size s)%nat by rewrite hs.
have hlt4 : (4 < size s)%nat by rewrite hs.
have hlt5 : (5 < size s)%nat by rewrite hs.
have htake k : (k < size s)%nat -> size (take k s) = k.
  move=> hk; rewrite size_take.
  by apply/minn_idPl; exact: ltnW hk.
have h0 : take 0 s \in R0 by rewrite /R0 take0 in_cons eqxx.
have h1 : take 1 s \in R1.
  rewrite /R1 (take_nth 0 hlt0).
  apply: (@extend_regressive_mem R0 (take 0 s) (nth 0 s 0)); first exact h0.
  by rewrite (htake 0 hlt0); apply: hreg.
have h2 : take 2 s \in R2.
  rewrite /R2 (take_nth 0 hlt1).
  apply: (@extend_regressive_mem R1 (take 1 s) (nth 0 s 1)); first exact h1.
  by rewrite (htake 1 hlt1); apply: hreg.
have h3 : take 3 s \in R3.
  rewrite /R3 (take_nth 0 hlt2).
  apply: (@extend_regressive_mem R2 (take 2 s) (nth 0 s 2)); first exact h2.
  by rewrite (htake 2 hlt2); apply: hreg.
have h4 : take 4 s \in R4.
  rewrite /R4 (take_nth 0 hlt3).
  apply: (@extend_regressive_mem R3 (take 3 s) (nth 0 s 3)); first exact h3.
  by rewrite (htake 3 hlt3); apply: hreg.
have h5 : take 5 s \in R5.
  rewrite /R5 (take_nth 0 hlt4).
  apply: (@extend_regressive_mem R4 (take 4 s) (nth 0 s 4)); first exact h4.
  by rewrite (htake 4 hlt4); apply: hreg.
have h6 : take 6 s \in R6.
  rewrite /R6 (take_nth 0 hlt5).
  apply: (@extend_regressive_mem R5 (take 5 s) (nth 0 s 5)); first exact h5.
  by rewrite (htake 5 hlt5); apply: hreg.
rewrite /regressive_lists /regressive_lists_from -/R0 -/R1 -/R2 -/R3
  -/R4 -/R5 -/R6.
have htake6 : take 6 s = s.
  have htake6' := take_size s.
  by rewrite hs in htake6'.
by rewrite -htake6.
Qed.

Definition canonical_kernel_code (f : seq nat) : seq nat :=
  [seq index (nth 0 f i) f | i <- six_naturals].

Lemma size_canonical_kernel_code f : size (canonical_kernel_code f) = 6.
Proof. by rewrite /canonical_kernel_code /six_naturals size_map size_iota. Qed.

Lemma nth_canonical_kernel_code f i :
  (i < 6)%nat ->
  nth 0 (canonical_kernel_code f) i = index (nth 0 f i) f.
Proof.
move=> hi.
rewrite /canonical_kernel_code (nth_map 0) ?size_iota //.
by rewrite /six_naturals nth_iota // add0n.
Qed.

Lemma canonical_kernel_code_regressive f :
  size f = 6 ->
  forall i, (i < 6)%nat ->
    (nth 0 (canonical_kernel_code f) i <= i)%nat.
Proof.
move=> hf i hi; rewrite nth_canonical_kernel_code //.
apply: index_nth.
by rewrite hf.
Qed.

Lemma canonical_kernel_code_idempotent f :
  size f = 6 -> partition_codeb (canonical_kernel_code f).
Proof.
move=> hf; apply/allP=> i hi.
rewrite /six_naturals mem_iota add0n in hi.
move/andP: hi=> [_ hi].
have hci := nth_canonical_kernel_code f hi.
have hindex_le := canonical_kernel_code_regressive hf hi.
have hindex_lt :
    (nth 0 (canonical_kernel_code f) i < 6)%nat :=
  leq_ltn_trans hindex_le hi.
rewrite hci in hindex_lt *.
rewrite (nth_canonical_kernel_code f hindex_lt).
apply/eqP.
congr (index _ f).
apply: nth_index.
apply: mem_nth.
by rewrite hf.
Qed.

Lemma canonical_kernel_code_mem f :
  size f = 6 -> canonical_kernel_code f \in partition_codes.
Proof.
move=> hf; rewrite /partition_codes mem_filter.
apply/andP; split.
  exact: canonical_kernel_code_idempotent hf.
apply: (@regressive_lists_complete (canonical_kernel_code f)).
  exact: size_canonical_kernel_code.
exact: canonical_kernel_code_regressive hf.
Qed.

Lemma canonical_kernel_code_eq f i j :
  size f = 6 -> (i < 6)%nat -> (j < 6)%nat ->
  (nth 0 (canonical_kernel_code f) i ==
     nth 0 (canonical_kernel_code f) j) =
  (nth 0 f i == nth 0 f j).
Proof.
move=> hf hi hj.
rewrite !nth_canonical_kernel_code //.
apply/eqP/eqP.
  apply: (index_inj 0).
    apply: (mem_nth 0); by rewrite hf.
    apply: (mem_nth 0); by rewrite hf.
move=> ->; exact: erefl.
Qed.

Lemma mem_six_naturals_lt i : i \in six_naturals -> (i < 6)%nat.
Proof.
rewrite /six_naturals mem_iota add0n.
by move/andP=> [_ hi].
Qed.

Lemma code_refines_kernel_canonical s f :
  size f = 6 ->
  code_refines_kernel s (canonical_kernel_code f) =
    code_refines_kernel s f.
Proof.
move=> hf; rewrite /code_refines_kernel.
apply: eq_in_all=> i hi.
apply: eq_in_all=> j hj.
by rewrite (canonical_kernel_code_eq hf (mem_six_naturals_lt hi)
  (mem_six_naturals_lt hj)).
Qed.

Lemma kernel_mobius_sum_canonical f :
  size f = 6 ->
  kernel_mobius_sum (canonical_kernel_code f) = kernel_mobius_sum f.
Proof.
move=> hf.
have hfilter :
    [seq s <- partition_codes |
       code_refines_kernel s (canonical_kernel_code f)] =
    [seq s <- partition_codes | code_refines_kernel s f].
  apply: eq_in_filter=> s _.
  exact: code_refines_kernel_canonical hf.
by rewrite /kernel_mobius_sum hfilter.
Qed.

Lemma kernel_mobius_positive_sum_canonical f :
  size f = 6 ->
  kernel_mobius_positive_sum (canonical_kernel_code f) =
    kernel_mobius_positive_sum f.
Proof.
move=> hf.
have hfilter :
    [seq s <- partition_codes |
       code_refines_kernel s (canonical_kernel_code f)] =
    [seq s <- partition_codes | code_refines_kernel s f].
  apply: eq_in_filter=> s _.
  exact: code_refines_kernel_canonical hf.
by rewrite /kernel_mobius_positive_sum hfilter.
Qed.

Lemma kernel_mobius_negative_sum_canonical f :
  size f = 6 ->
  kernel_mobius_negative_sum (canonical_kernel_code f) =
    kernel_mobius_negative_sum f.
Proof.
move=> hf.
have hfilter :
    [seq s <- partition_codes |
       code_refines_kernel s (canonical_kernel_code f)] =
    [seq s <- partition_codes | code_refines_kernel s f].
  apply: eq_in_filter=> s _.
  exact: code_refines_kernel_canonical hf.
by rewrite /kernel_mobius_negative_sum hfilter.
Qed.

Lemma uniq_canonical_kernel_code f :
  size f = 6 -> uniq (canonical_kernel_code f) = uniq f.
Proof.
move=> hf; apply/idP/idP.
  move/uniqP=> hc; apply/uniqP=> i j hi hj hij.
  have hi6 : (i < 6)%nat by move: hi; rewrite hf.
  have hj6 : (j < 6)%nat by move: hj; rewrite hf.
  apply: hc.
    by rewrite size_canonical_kernel_code.
    by rewrite size_canonical_kernel_code.
  have hbool :
      nth 0 (canonical_kernel_code f) i ==
        nth 0 (canonical_kernel_code f) j.
    rewrite (canonical_kernel_code_eq hf hi6 hj6).
    apply/eqP; exact hij.
  move/eqP: hbool=> hbool; exact hbool.
move/uniqP=> hfuniq; apply/uniqP=> i j hi hj hij.
have hi6 : (i < 6)%nat by move: hi; rewrite size_canonical_kernel_code.
have hj6 : (j < 6)%nat by move: hj; rewrite size_canonical_kernel_code.
apply: hfuniq.
  by rewrite hf.
  by rewrite hf.
have hbool : nth 0 f i == nth 0 f j.
  rewrite -(canonical_kernel_code_eq hf hi6 hj6).
  apply/eqP; exact hij.
move/eqP: hbool=> hbool; exact hbool.
Qed.

Example partition_count_is_203 : partition_count = 203%nat.
Proof. by vm_compute. Qed.

Lemma kernel_mobius_identities_nth n :
  (n < 203)%nat ->
  let f := nth [::] partition_codes n in
  (kernel_mobius_sum f = if code_injectiveb f then 1%Z else 0%Z) /\
  (if code_injectiveb f then
     kernel_mobius_positive_sum f =
       (kernel_mobius_negative_sum f).+1
   else
     kernel_mobius_positive_sum f = kernel_mobius_negative_sum f).
Proof.
move=> hn.
have hn' : Peano.lt n 203 by exact/ltP.
have hcases : n = 0%nat \/ n = 1%nat \/ n = 2%nat \/ n = 3%nat \/ n = 4%nat \/ n = 5%nat \/ n = 6%nat \/ n = 7%nat \/ n = 8%nat \/ n = 9%nat \/ n = 10%nat \/ n = 11%nat \/ n = 12%nat \/ n = 13%nat \/ n = 14%nat \/ n = 15%nat \/ n = 16%nat \/ n = 17%nat \/ n = 18%nat \/ n = 19%nat \/ n = 20%nat \/ n = 21%nat \/ n = 22%nat \/ n = 23%nat \/ n = 24%nat \/ n = 25%nat \/ n = 26%nat \/ n = 27%nat \/ n = 28%nat \/ n = 29%nat \/ n = 30%nat \/ n = 31%nat \/ n = 32%nat \/ n = 33%nat \/ n = 34%nat \/ n = 35%nat \/ n = 36%nat \/ n = 37%nat \/ n = 38%nat \/ n = 39%nat \/ n = 40%nat \/ n = 41%nat \/ n = 42%nat \/ n = 43%nat \/ n = 44%nat \/ n = 45%nat \/ n = 46%nat \/ n = 47%nat \/ n = 48%nat \/ n = 49%nat \/ n = 50%nat \/ n = 51%nat \/ n = 52%nat \/ n = 53%nat \/ n = 54%nat \/ n = 55%nat \/ n = 56%nat \/ n = 57%nat \/ n = 58%nat \/ n = 59%nat \/ n = 60%nat \/ n = 61%nat \/ n = 62%nat \/ n = 63%nat \/ n = 64%nat \/ n = 65%nat \/ n = 66%nat \/ n = 67%nat \/ n = 68%nat \/ n = 69%nat \/ n = 70%nat \/ n = 71%nat \/ n = 72%nat \/ n = 73%nat \/ n = 74%nat \/ n = 75%nat \/ n = 76%nat \/ n = 77%nat \/ n = 78%nat \/ n = 79%nat \/ n = 80%nat \/ n = 81%nat \/ n = 82%nat \/ n = 83%nat \/ n = 84%nat \/ n = 85%nat \/ n = 86%nat \/ n = 87%nat \/ n = 88%nat \/ n = 89%nat \/ n = 90%nat \/ n = 91%nat \/ n = 92%nat \/ n = 93%nat \/ n = 94%nat \/ n = 95%nat \/ n = 96%nat \/ n = 97%nat \/ n = 98%nat \/ n = 99%nat \/ n = 100%nat \/ n = 101%nat \/ n = 102%nat \/ n = 103%nat \/ n = 104%nat \/ n = 105%nat \/ n = 106%nat \/ n = 107%nat \/ n = 108%nat \/ n = 109%nat \/ n = 110%nat \/ n = 111%nat \/ n = 112%nat \/ n = 113%nat \/ n = 114%nat \/ n = 115%nat \/ n = 116%nat \/ n = 117%nat \/ n = 118%nat \/ n = 119%nat \/ n = 120%nat \/ n = 121%nat \/ n = 122%nat \/ n = 123%nat \/ n = 124%nat \/ n = 125%nat \/ n = 126%nat \/ n = 127%nat \/ n = 128%nat \/ n = 129%nat \/ n = 130%nat \/ n = 131%nat \/ n = 132%nat \/ n = 133%nat \/ n = 134%nat \/ n = 135%nat \/ n = 136%nat \/ n = 137%nat \/ n = 138%nat \/ n = 139%nat \/ n = 140%nat \/ n = 141%nat \/ n = 142%nat \/ n = 143%nat \/ n = 144%nat \/ n = 145%nat \/ n = 146%nat \/ n = 147%nat \/ n = 148%nat \/ n = 149%nat \/ n = 150%nat \/ n = 151%nat \/ n = 152%nat \/ n = 153%nat \/ n = 154%nat \/ n = 155%nat \/ n = 156%nat \/ n = 157%nat \/ n = 158%nat \/ n = 159%nat \/ n = 160%nat \/ n = 161%nat \/ n = 162%nat \/ n = 163%nat \/ n = 164%nat \/ n = 165%nat \/ n = 166%nat \/ n = 167%nat \/ n = 168%nat \/ n = 169%nat \/ n = 170%nat \/ n = 171%nat \/ n = 172%nat \/ n = 173%nat \/ n = 174%nat \/ n = 175%nat \/ n = 176%nat \/ n = 177%nat \/ n = 178%nat \/ n = 179%nat \/ n = 180%nat \/ n = 181%nat \/ n = 182%nat \/ n = 183%nat \/ n = 184%nat \/ n = 185%nat \/ n = 186%nat \/ n = 187%nat \/ n = 188%nat \/ n = 189%nat \/ n = 190%nat \/ n = 191%nat \/ n = 192%nat \/ n = 193%nat \/ n = 194%nat \/ n = 195%nat \/ n = 196%nat \/ n = 197%nat \/ n = 198%nat \/ n = 199%nat \/ n = 200%nat \/ n = 201%nat \/ n = 202%nat by lia.
repeat match goal with
| h : _ \/ _ |- _ =>
    destruct h as [h | h]; [subst n; split; vm_compute; reflexivity |]
| h : ?x = _ |- _ => subst x; split; vm_compute; reflexivity
end.
Qed.

Lemma kernel_mobius_identity_nth n :
  (n < 203)%nat ->
  let f := nth [::] partition_codes n in
  kernel_mobius_sum f = if code_injectiveb f then 1%Z else 0%Z.
Proof. by move=> hn; exact: (kernel_mobius_identities_nth hn).1. Qed.

Lemma kernel_mobius_signed_identity_nth n :
  (n < 203)%nat ->
  let f := nth [::] partition_codes n in
  if code_injectiveb f then
    kernel_mobius_positive_sum f = (kernel_mobius_negative_sum f).+1
  else
    kernel_mobius_positive_sum f = kernel_mobius_negative_sum f.
Proof. by move=> hn; exact: (kernel_mobius_identities_nth hn).2. Qed.

Lemma kernel_mobius_identity_on_code f :
  f \in partition_codes ->
  kernel_mobius_sum f = if code_injectiveb f then 1%Z else 0%Z.
Proof.
move=> hf.
have hn : is_true (leq (index f partition_codes).+1 203).
  by rewrite -partition_count_is_203 /partition_count index_mem.
move: (kernel_mobius_identity_nth hn).
by rewrite (nth_index [::] hf).
Qed.

Lemma kernel_mobius_signed_identity_on_code f :
  f \in partition_codes ->
  if code_injectiveb f then
    kernel_mobius_positive_sum f = (kernel_mobius_negative_sum f).+1
  else
    kernel_mobius_positive_sum f = kernel_mobius_negative_sum f.
Proof.
move=> hf.
have hn : is_true (leq (index f partition_codes).+1 203).
  by rewrite -partition_count_is_203 /partition_count index_mem.
move: (kernel_mobius_signed_identity_nth hn).
by rewrite (nth_index [::] hf).
Qed.

(** The finite computation above is now available for every six-entry
    assignment, not only for the 203 canonical representatives.  The proof
    factors through the canonical equality-kernel code, so no enumeration of
    the [6^6] assignments is hidden here. *)
Theorem kernel_mobius_identity f :
  size f = 6 ->
  kernel_mobius_sum f = if code_injectiveb f then 1%Z else 0%Z.
Proof.
move=> hf.
move: (kernel_mobius_identity_on_code (canonical_kernel_code_mem hf)).
by rewrite /code_injectiveb (kernel_mobius_sum_canonical hf)
  (uniq_canonical_kernel_code hf).
Qed.

Theorem kernel_mobius_signed_identity f :
  size f = 6 ->
  if code_injectiveb f then
    kernel_mobius_positive_sum f = (kernel_mobius_negative_sum f).+1
  else
    kernel_mobius_positive_sum f = kernel_mobius_negative_sum f.
Proof.
move=> hf.
move: (kernel_mobius_signed_identity_on_code
  (canonical_kernel_code_mem hf)).
by rewrite /code_injectiveb
  (kernel_mobius_positive_sum_canonical hf)
  (kernel_mobius_negative_sum_canonical hf)
  (uniq_canonical_kernel_code hf).
Qed.

Lemma foldr_addn_map_big (T : Type) (r : seq T) (F : T -> nat) :
  foldr addn 0 (map F r) = \sum_(x <- r) F x.
Proof. by elim: r=> [|x r IHr]; rewrite ?big_nil //= big_cons IHr. Qed.

Section RingValuedMobius.

Variable R : comPzRingType.

Definition partition_ring_weight (s : seq nat) : R :=
  (partition_mobius_positive s)%:R -
    (partition_mobius_negative s)%:R.

Lemma partition_ring_weight_sum f :
  size f = 6 ->
  \sum_(s <- partition_codes | code_refines_kernel s f)
      partition_ring_weight s =
    if code_injectiveb f then 1 else 0.
Proof.
move=> hf.
rewrite /partition_ring_weight sumrB -!natr_sum.
have hpos :
    \sum_(s <- partition_codes | code_refines_kernel s f)
      partition_mobius_positive s = kernel_mobius_positive_sum f.
  by rewrite -big_filter /kernel_mobius_positive_sum foldr_addn_map_big.
have hneg :
    \sum_(s <- partition_codes | code_refines_kernel s f)
      partition_mobius_negative s = kernel_mobius_negative_sum f.
  by rewrite -big_filter /kernel_mobius_negative_sum foldr_addn_map_big.
rewrite hpos hneg.
have hsigned := kernel_mobius_signed_identity hf.
case huniq: (code_injectiveb f).
  rewrite huniq in hsigned *.
  rewrite hsigned -addn1 natrD.
  apply: (addIr ((kernel_mobius_negative_sum f)%:R : R)).
  rewrite subrK addrC.
  reflexivity.
rewrite huniq in hsigned *.
by rewrite hsigned subrr.
Qed.

Definition root_assignment := {ffun root_index -> root_index}.

Definition assignment_code (a : root_assignment) : seq nat :=
  [seq val (a (inord i)) | i <- six_naturals].

Lemma size_assignment_code a : size (assignment_code a) = 6.
Proof. by rewrite /assignment_code /six_naturals size_map size_iota. Qed.

Lemma nth_assignment_code a i :
  (i < 6)%nat ->
  nth 0 (assignment_code a) i = val (a (inord i)).
Proof.
move=> hi.
rewrite /assignment_code (nth_map 0) ?size_iota //.
by rewrite /six_naturals nth_iota // add0n.
Qed.

Lemma nth_assignment_code_ord a (i : root_index) :
  nth 0 (assignment_code a) i = val (a i).
Proof. by rewrite nth_assignment_code // inord_val. Qed.

Lemma partition_code_label_lt s (hs : s \in partition_codes)
    (i : root_index) : (nth 0 s i < 6)%nat.
Proof.
exact: leq_ltn_trans (partition_code_regressive hs (ltn_ord i))
  (ltn_ord i).
Qed.

Lemma partition_code_nth_idempotent s (hs : s \in partition_codes)
    (i : root_index) : nth 0 s (nth 0 s i) = nth 0 s i.
Proof.
move/allP: (partition_code_idempotent hs)=> hid.
have hi : val i \in six_naturals.
  by rewrite /six_naturals mem_iota add0n ltn_ord.
exact/eqP/(hid (val i) hi).
Qed.

(** Active blocks are the canonical labels that actually occur in the
    partition code. *)
Definition active_block (s : seq nat) :=
  {j : root_index | val j \in s}.

Definition position_block s (hs : s \in partition_codes)
    (i : root_index) : active_block s.
Proof.
apply: (Sub (inord (nth 0 s i)) _).
change (nat_of_ord (inord (nth 0 s i) : root_index) \in s).
rewrite (inordK (partition_code_label_lt hs i)).
apply: mem_nth.
by rewrite partition_code_size // ltn_ord.
Defined.

Lemma val_position_block s (hs : s \in partition_codes) i :
  val (val (position_block hs i)) = nth 0 s i.
Proof.
by rewrite /position_block /= (inordK (partition_code_label_lt hs i)).
Qed.

Lemma partition_code_active_idempotent s
    (hs : s \in partition_codes) (j : active_block s) :
  nth 0 s (val (val j)) = val (val j).
Proof.
have hjlt_size : (index (val (val j)) s < size s)%nat.
  by rewrite index_mem; exact: valP j.
have hjlt : (index (val (val j)) s < 6)%nat.
  by move: hjlt_size; rewrite (partition_code_size hs).
pose i : root_index := Ordinal hjlt.
have hid := partition_code_nth_idempotent hs i.
rewrite /i /= (nth_index 0 (valP j)) in hid.
exact hid.
Qed.

Definition block_choice (s : seq nat) :=
  {ffun active_block s -> root_index}.

Definition assignment_of_blocks s (hs : s \in partition_codes)
    (b : block_choice s) : root_assignment :=
  [ffun i => b (position_block hs i)].

Definition blocks_of_assignment s (a : root_assignment) : block_choice s :=
  [ffun j => a (val j)].

Lemma code_refines_kernel_ord s a (i j : root_index) :
  code_refines_kernel s (assignment_code a) ->
  nth 0 s i = nth 0 s j -> a i = a j.
Proof.
move/allP=> href hsij.
have hi : val i \in six_naturals.
  by rewrite /six_naturals mem_iota add0n ltn_ord.
have hj : val j \in six_naturals.
  by rewrite /six_naturals mem_iota add0n ltn_ord.
move/allP: (href (val i) hi)=> hrefi.
move/implyP: (hrefi (val j) hj)=> hrefij.
have hsijb : nth 0 s (val i) == nth 0 s (val j).
  by apply/eqP; exact hsij.
have hcodes :
    nth 0 (assignment_code a) (val i) ==
      nth 0 (assignment_code a) (val j) :=
  hrefij hsijb.
move/eqP: hcodes.
by rewrite !nth_assignment_code_ord=> /val_inj.
Qed.

Lemma blocks_assignmentK s (hs : s \in partition_codes) :
  cancel (assignment_of_blocks hs) (blocks_of_assignment s).
Proof.
move=> b; apply/ffunP=> j.
rewrite /blocks_of_assignment /assignment_of_blocks !ffunE.
congr (b _); apply: val_inj; apply: val_inj; rewrite val_position_block.
exact: partition_code_active_idempotent hs j.
Qed.

Lemma assignment_of_blocks_refines s (hs : s \in partition_codes)
    (b : block_choice s) :
  code_refines_kernel s (assignment_code (assignment_of_blocks hs b)).
Proof.
apply/allP=> i hi; apply/allP=> j hj; apply/implyP=> hij.
have hi6 := mem_six_naturals_lt hi.
have hj6 := mem_six_naturals_lt hj.
rewrite (@nth_assignment_code (assignment_of_blocks hs b) i hi6)
  (@nth_assignment_code (assignment_of_blocks hs b) j hj6).
apply/eqP.
rewrite /assignment_of_blocks !ffunE.
congr (val (b _)); apply: val_inj; apply: val_inj.
rewrite !val_position_block !inordK //.
exact/eqP/hij.
Qed.

Definition refining_assignment (s : seq nat) :=
  {a : root_assignment |
    code_refines_kernel s (assignment_code a)}.

Definition refining_assignment_of_blocks s
    (hs : s \in partition_codes) (b : block_choice s) :
    refining_assignment s :=
  Sub (assignment_of_blocks hs b) (assignment_of_blocks_refines hs b).

Definition blocks_of_refining_assignment s (a : refining_assignment s) :
    block_choice s := blocks_of_assignment s (val a).

Lemma refining_assignment_blocksK s (hs : s \in partition_codes) :
  cancel (@blocks_of_refining_assignment s)
    (@refining_assignment_of_blocks s hs).
Proof.
move=> a; apply: val_inj; apply/ffunP=> i.
rewrite /refining_assignment_of_blocks /blocks_of_refining_assignment
  /assignment_of_blocks /blocks_of_assignment /= !ffunE.
symmetry.
apply: (@code_refines_kernel_ord s (val a) i
  (val (position_block hs i)) (valP a)).
change (nth 0 s i = nth 0 s (val (val (position_block hs i)))).
rewrite val_position_block.
exact: esym (partition_code_nth_idempotent hs i).
Qed.

Lemma refining_assignment_bijective s (hs : s \in partition_codes) :
  bijective (@refining_assignment_of_blocks s hs).
Proof.
apply: (@Bijective _ _ (@refining_assignment_of_blocks s hs)
  (@blocks_of_refining_assignment s)).
- exact: blocks_assignmentK hs.
- exact: refining_assignment_blocksK hs.
Qed.

Definition assignment_monomial
    (roots : 6.-tuple R) (e : sparse_exponent) (a : root_assignment) : R :=
  \prod_(i : root_index) tnth roots (a i) ^+ tnth e i.

Definition block_exponent (e : sparse_exponent) (s : seq nat)
    (j : active_block s) : nat :=
  \sum_(i : root_index | nth 0 s i == val (val j)) tnth e i.

Definition root_power_sum (roots : 6.-tuple R) (n : nat) : R :=
  \sum_(k : root_index) tnth roots k ^+ n.

Definition partition_power_product
    (roots : 6.-tuple R) (e : sparse_exponent) (s : seq nat) : R :=
  \prod_(j : active_block s)
    root_power_sum roots (block_exponent e j).

Lemma position_block_eq s (hs : s \in partition_codes)
    (i : root_index) (j : active_block s) :
  (position_block hs i == j) =
    (nth 0 s i == val (val j)).
Proof.
apply/eqP/eqP.
- move=> hij.
  have hval := congr1 (fun x : active_block s => val (val x)) hij.
  by rewrite val_position_block in hval.
- move=> hij; apply: val_inj; apply: val_inj.
  by rewrite val_position_block.
Qed.

Lemma assignment_monomial_of_blocks roots e s
    (hs : s \in partition_codes) (b : block_choice s) :
  assignment_monomial roots e (assignment_of_blocks hs b) =
    \prod_(j : active_block s)
      tnth roots (b j) ^+ block_exponent e j.
Proof.
rewrite /assignment_monomial /block_exponent.
under [RHS]eq_bigr => j _ do rewrite expr_sum.
rewrite (@partition_big _ _ _ _ _ _ predT (position_block hs) predT _) //=.
apply: eq_bigr=> j _.
apply: eq_big.
- exact: (fun i => position_block_eq hs i j).
- move=> i hij.
have hp : position_block hs i = j.
  exact/eqP/hij.
by rewrite /assignment_of_blocks ffunE hp.
Qed.

Definition partition_assignment_sum
    (roots : 6.-tuple R) (e : sparse_exponent) (s : seq nat) : R :=
  \sum_(a : root_assignment | code_refines_kernel s (assignment_code a))
    assignment_monomial roots e a.

Theorem partition_assignment_sumE roots e s
    (hs : s \in partition_codes) :
  partition_assignment_sum roots e s =
    partition_power_product roots e s.
Proof.
rewrite /partition_assignment_sum big_sub /partition_power_product
  /root_power_sum bigA_distr_bigA.
rewrite (reindex _
  (onW_bij predT (refining_assignment_bijective hs))).
apply: eq_bigr=> b _.
exact: assignment_monomial_of_blocks hs b.
Qed.

Definition injective_assignment_sum
    (roots : 6.-tuple R) (e : sparse_exponent) : R :=
  \sum_(a : root_assignment | code_injectiveb (assignment_code a))
    assignment_monomial roots e a.

Definition mobius_weighted_assignment_sum
    (roots : 6.-tuple R) (e : sparse_exponent) : R :=
  \sum_(s <- partition_codes)
    partition_ring_weight s * partition_assignment_sum roots e s.

Theorem mobius_weighted_assignment_sumE roots e :
  mobius_weighted_assignment_sum roots e =
    injective_assignment_sum roots e.
Proof.
rewrite /mobius_weighted_assignment_sum /partition_assignment_sum
  /injective_assignment_sum.
under eq_bigr => s _ do rewrite mulr_sumr big_mkcond.
rewrite exchange_big [RHS]big_mkcond.
apply: eq_bigr=> a _.
transitivity
  ((\sum_(s <- partition_codes |
       code_refines_kernel s (assignment_code a))
       partition_ring_weight s) * assignment_monomial roots e a).
  rewrite big_distrl [RHS]big_mkcond.
  apply: eq_bigr=> s _.
  by case: (code_refines_kernel s (assignment_code a));
    rewrite ?mul0r.
rewrite partition_ring_weight_sum ?size_assignment_code.
by case: (code_injectiveb (assignment_code a));
  rewrite ?mul1r ?mul0r.
done.
Qed.

Definition mobius_power_sum_formula
    (roots : 6.-tuple R) (e : sparse_exponent) : R :=
  \sum_(s <- partition_codes)
    partition_ring_weight s * partition_power_product roots e s.

(** Every six-variable injective monomial orbit is now an explicit integer
    combination of products of ordinary power sums. *)
Theorem injective_assignment_sum_power_formula roots e :
  injective_assignment_sum roots e = mobius_power_sum_formula roots e.
Proof.
rewrite -mobius_weighted_assignment_sumE
  /mobius_weighted_assignment_sum /mobius_power_sum_formula.
apply: eq_big_seq=> s hs.
by rewrite (partition_assignment_sumE roots e hs).
Qed.

End RingValuedMobius.

End PolynomialFormulasSexticPowerSumSymmetric.
