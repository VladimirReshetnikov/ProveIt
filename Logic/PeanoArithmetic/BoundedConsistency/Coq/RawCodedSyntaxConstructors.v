(**
  Raw-model semantics for the canonical polynomial syntax constructors.

  The executable syntax checker uses [PAListCode.listCode]: a nonempty list
  is represented by [1 + ((head + tail)^2 + head)].  Standard-model graph
  formula selection is not adequate for nonstandard proof codes, so this
  file exposes the constructor equations themselves as transparent PA terms
  and formulae and proves their exact semantics in every law-free raw
  arithmetic structure.

  The resulting relations accept arbitrary carrier elements as recursive
  child codes.  They are therefore suitable as the local constructor layer
  of a later beta-traced well-formedness/rank computation over nonstandard
  codes.  PA is used only for the final quotation theorem identifying these
  raw constructor folds with the original external natural-number codes.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import CodedSyntax.

Import ListNotations.

Module PABoundedRawCodedSyntaxConstructors.

Import PA.
Import PAListCode.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.

(** ------------------------------------------------------------------
    Polynomial list nodes. *)

Definition rawPolynomialPair (M : RawPAModel) (a b : M) : M :=
  raw_add M (raw_mul M (raw_add M a b) (raw_add M a b)) a.

Definition rawListNode (M : RawPAModel) (head tail : M) : M :=
  raw_succ M (rawPolynomialPair M head tail).

Arguments rawPolynomialPair M a b : clear implicits.
Arguments rawListNode M head tail : clear implicits.

Fixpoint rawListCode (M : RawPAModel) (xs : list M) : M :=
  match xs with
  | [] => raw_zero M
  | head :: tail => rawListNode M head (rawListCode M tail)
  end.

Arguments rawListCode M xs : clear implicits.

Definition codeList1Term (x : term) : term :=
  nodeTerm x tZero.

Definition codeList2Term (x y : term) : term :=
  nodeTerm x (codeList1Term y).

Definition codeList3Term (x y z : term) : term :=
  nodeTerm x (codeList2Term y z).

Definition rawCodeList1 (M : RawPAModel) (x : M) : M :=
  rawListCode M [x].

Definition rawCodeList2 (M : RawPAModel) (x y : M) : M :=
  rawListCode M [x; y].

Definition rawCodeList3 (M : RawPAModel) (x y z : M) : M :=
  rawListCode M [x; y; z].

Arguments rawCodeList1 M x : clear implicits.
Arguments rawCodeList2 M x y : clear implicits.
Arguments rawCodeList3 M x y z : clear implicits.

Lemma raw_eval_pairTerm : forall (M : RawPAModel) e a b,
  raw_term_eval M e (pairTerm a b) =
  rawPolynomialPair M (raw_term_eval M e a) (raw_term_eval M e b).
Proof. reflexivity. Qed.

Lemma raw_eval_nodeTerm : forall (M : RawPAModel) e head tail,
  raw_term_eval M e (nodeTerm head tail) =
  rawListNode M (raw_term_eval M e head) (raw_term_eval M e tail).
Proof. reflexivity. Qed.

Lemma raw_eval_codeList1Term : forall (M : RawPAModel) e x,
  raw_term_eval M e (codeList1Term x) =
  rawCodeList1 M (raw_term_eval M e x).
Proof. reflexivity. Qed.

Lemma raw_eval_codeList2Term : forall (M : RawPAModel) e x y,
  raw_term_eval M e (codeList2Term x y) =
  rawCodeList2 M (raw_term_eval M e x) (raw_term_eval M e y).
Proof. reflexivity. Qed.

Lemma raw_eval_codeList3Term : forall (M : RawPAModel) e x y z,
  raw_term_eval M e (codeList3Term x y z) =
  rawCodeList3 M (raw_term_eval M e x) (raw_term_eval M e y)
    (raw_term_eval M e z).
Proof. reflexivity. Qed.

(** Transparent graph formulae for the empty code and the first three list
    arities used by the syntax representation. *)
Definition listNilCodeTermAt (code : term) : formula :=
  pEq code tZero.

Definition listConsCodeTermAt
    (code head tail : term) : formula :=
  pEq code (nodeTerm head tail).

Definition codeList1TermAt (code x : term) : formula :=
  pEq code (codeList1Term x).

Definition codeList2TermAt (code x y : term) : formula :=
  pEq code (codeList2Term x y).

Definition codeList3TermAt (code x y z : term) : formula :=
  pEq code (codeList3Term x y z).

Lemma raw_sat_listNilCodeTermAt_iff : forall (M : RawPAModel) e code,
  raw_formula_sat M e (listNilCodeTermAt code) <->
  raw_term_eval M e code = raw_zero M.
Proof. reflexivity. Qed.

Lemma raw_sat_listConsCodeTermAt_iff : forall (M : RawPAModel)
    e code head tail,
  raw_formula_sat M e (listConsCodeTermAt code head tail) <->
  raw_term_eval M e code =
    rawListNode M (raw_term_eval M e head) (raw_term_eval M e tail).
Proof. reflexivity. Qed.

Lemma raw_sat_codeList1TermAt_iff : forall (M : RawPAModel) e code x,
  raw_formula_sat M e (codeList1TermAt code x) <->
  raw_term_eval M e code = rawCodeList1 M (raw_term_eval M e x).
Proof. reflexivity. Qed.

Lemma raw_sat_codeList2TermAt_iff : forall (M : RawPAModel) e code x y,
  raw_formula_sat M e (codeList2TermAt code x y) <->
  raw_term_eval M e code =
    rawCodeList2 M (raw_term_eval M e x) (raw_term_eval M e y).
Proof. reflexivity. Qed.

Lemma raw_sat_codeList3TermAt_iff : forall (M : RawPAModel) e code x y z,
  raw_formula_sat M e (codeList3TermAt code x y z) <->
  raw_term_eval M e code = rawCodeList3 M
    (raw_term_eval M e x) (raw_term_eval M e y) (raw_term_eval M e z).
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    PA term-code constructors. *)

Definition termVarCodeTermAt (code index : term) : formula :=
  codeList2TermAt code (Term.numeral 0) index.

Definition termZeroCodeTermAt (code : term) : formula :=
  codeList1TermAt code (Term.numeral 1).

Definition termSuccCodeTermAt (code child : term) : formula :=
  codeList2TermAt code (Term.numeral 2) child.

Definition termAddCodeTermAt (code left right : term) : formula :=
  codeList3TermAt code (Term.numeral 3) left right.

Definition termMulCodeTermAt (code left right : term) : formula :=
  codeList3TermAt code (Term.numeral 4) left right.

Definition rawTermVarCode (M : RawPAModel) (index : M) : M :=
  rawCodeList2 M (rawNumeralValue M 0) index.

Definition rawTermZeroCode (M : RawPAModel) : M :=
  rawCodeList1 M (rawNumeralValue M 1).

Definition rawTermSuccCode (M : RawPAModel) (child : M) : M :=
  rawCodeList2 M (rawNumeralValue M 2) child.

Definition rawTermAddCode (M : RawPAModel) (left right : M) : M :=
  rawCodeList3 M (rawNumeralValue M 3) left right.

Definition rawTermMulCode (M : RawPAModel) (left right : M) : M :=
  rawCodeList3 M (rawNumeralValue M 4) left right.

Arguments rawTermVarCode M index : clear implicits.
Arguments rawTermZeroCode M : clear implicits.
Arguments rawTermSuccCode M child : clear implicits.
Arguments rawTermAddCode M left right : clear implicits.
Arguments rawTermMulCode M left right : clear implicits.

Lemma raw_sat_termVarCodeTermAt_iff : forall (M : RawPAModel) e code index,
  raw_formula_sat M e (termVarCodeTermAt code index) <->
  raw_term_eval M e code = rawTermVarCode M (raw_term_eval M e index).
Proof.
  intros. unfold termVarCodeTermAt, rawTermVarCode.
  rewrite raw_sat_codeList2TermAt_iff, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_sat_termZeroCodeTermAt_iff : forall (M : RawPAModel) e code,
  raw_formula_sat M e (termZeroCodeTermAt code) <->
  raw_term_eval M e code = rawTermZeroCode M.
Proof.
  intros. unfold termZeroCodeTermAt, rawTermZeroCode.
  rewrite raw_sat_codeList1TermAt_iff, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_sat_termSuccCodeTermAt_iff : forall (M : RawPAModel) e code child,
  raw_formula_sat M e (termSuccCodeTermAt code child) <->
  raw_term_eval M e code = rawTermSuccCode M (raw_term_eval M e child).
Proof.
  intros. unfold termSuccCodeTermAt, rawTermSuccCode.
  rewrite raw_sat_codeList2TermAt_iff, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_sat_termAddCodeTermAt_iff : forall (M : RawPAModel)
    e code left right,
  raw_formula_sat M e (termAddCodeTermAt code left right) <->
  raw_term_eval M e code = rawTermAddCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold termAddCodeTermAt, rawTermAddCode.
  rewrite raw_sat_codeList3TermAt_iff, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_sat_termMulCodeTermAt_iff : forall (M : RawPAModel)
    e code left right,
  raw_formula_sat M e (termMulCodeTermAt code left right) <->
  raw_term_eval M e code = rawTermMulCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold termMulCodeTermAt, rawTermMulCode.
  rewrite raw_sat_codeList3TermAt_iff, raw_term_eval_numeral. reflexivity.
Qed.

(** ------------------------------------------------------------------
    PA formula-code constructors. *)

Definition formulaEqCodeTermAt (code left right : term) : formula :=
  codeList3TermAt code (Term.numeral 0) left right.

Definition formulaBotCodeTermAt (code : term) : formula :=
  codeList1TermAt code (Term.numeral 1).

Definition formulaImpCodeTermAt (code left right : term) : formula :=
  codeList3TermAt code (Term.numeral 2) left right.

Definition formulaAndCodeTermAt (code left right : term) : formula :=
  codeList3TermAt code (Term.numeral 3) left right.

Definition formulaOrCodeTermAt (code left right : term) : formula :=
  codeList3TermAt code (Term.numeral 4) left right.

Definition formulaAllCodeTermAt (code child : term) : formula :=
  codeList2TermAt code (Term.numeral 5) child.

Definition formulaExCodeTermAt (code child : term) : formula :=
  codeList2TermAt code (Term.numeral 6) child.

Definition rawFormulaEqCode (M : RawPAModel) (left right : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) left right.

Definition rawFormulaBotCode (M : RawPAModel) : M :=
  rawCodeList1 M (rawNumeralValue M 1).

Definition rawFormulaImpCode (M : RawPAModel) (left right : M) : M :=
  rawCodeList3 M (rawNumeralValue M 2) left right.

Definition rawFormulaAndCode (M : RawPAModel) (left right : M) : M :=
  rawCodeList3 M (rawNumeralValue M 3) left right.

Definition rawFormulaOrCode (M : RawPAModel) (left right : M) : M :=
  rawCodeList3 M (rawNumeralValue M 4) left right.

Definition rawFormulaAllCode (M : RawPAModel) (child : M) : M :=
  rawCodeList2 M (rawNumeralValue M 5) child.

Definition rawFormulaExCode (M : RawPAModel) (child : M) : M :=
  rawCodeList2 M (rawNumeralValue M 6) child.

Arguments rawFormulaEqCode M left right : clear implicits.
Arguments rawFormulaBotCode M : clear implicits.
Arguments rawFormulaImpCode M left right : clear implicits.
Arguments rawFormulaAndCode M left right : clear implicits.
Arguments rawFormulaOrCode M left right : clear implicits.
Arguments rawFormulaAllCode M child : clear implicits.
Arguments rawFormulaExCode M child : clear implicits.

Lemma raw_sat_formulaEqCodeTermAt_iff : forall (M : RawPAModel)
    e code left right,
  raw_formula_sat M e (formulaEqCodeTermAt code left right) <->
  raw_term_eval M e code = rawFormulaEqCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold formulaEqCodeTermAt, rawFormulaEqCode.
  rewrite raw_sat_codeList3TermAt_iff, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_sat_formulaBotCodeTermAt_iff : forall (M : RawPAModel) e code,
  raw_formula_sat M e (formulaBotCodeTermAt code) <->
  raw_term_eval M e code = rawFormulaBotCode M.
Proof.
  intros. unfold formulaBotCodeTermAt, rawFormulaBotCode.
  rewrite raw_sat_codeList1TermAt_iff, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_sat_formulaImpCodeTermAt_iff : forall (M : RawPAModel)
    e code left right,
  raw_formula_sat M e (formulaImpCodeTermAt code left right) <->
  raw_term_eval M e code = rawFormulaImpCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold formulaImpCodeTermAt, rawFormulaImpCode.
  rewrite raw_sat_codeList3TermAt_iff, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_sat_formulaAndCodeTermAt_iff : forall (M : RawPAModel)
    e code left right,
  raw_formula_sat M e (formulaAndCodeTermAt code left right) <->
  raw_term_eval M e code = rawFormulaAndCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold formulaAndCodeTermAt, rawFormulaAndCode.
  rewrite raw_sat_codeList3TermAt_iff, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_sat_formulaOrCodeTermAt_iff : forall (M : RawPAModel)
    e code left right,
  raw_formula_sat M e (formulaOrCodeTermAt code left right) <->
  raw_term_eval M e code = rawFormulaOrCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold formulaOrCodeTermAt, rawFormulaOrCode.
  rewrite raw_sat_codeList3TermAt_iff, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_sat_formulaAllCodeTermAt_iff : forall (M : RawPAModel)
    e code child,
  raw_formula_sat M e (formulaAllCodeTermAt code child) <->
  raw_term_eval M e code = rawFormulaAllCode M (raw_term_eval M e child).
Proof.
  intros. unfold formulaAllCodeTermAt, rawFormulaAllCode.
  rewrite raw_sat_codeList2TermAt_iff, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_sat_formulaExCodeTermAt_iff : forall (M : RawPAModel)
    e code child,
  raw_formula_sat M e (formulaExCodeTermAt code child) <->
  raw_term_eval M e code = rawFormulaExCode M (raw_term_eval M e child).
Proof.
  intros. unfold formulaExCodeTermAt, rawFormulaExCode.
  rewrite raw_sat_codeList2TermAt_iff, raw_term_eval_numeral. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Quotation into an arbitrary raw model and agreement with the original
    external codes at standard syntax. *)

Fixpoint rawQuotedTermCode (M : RawPAModel) (t : term) : M :=
  match t with
  | tVar n => rawTermVarCode M (rawNumeralValue M n)
  | tZero => rawTermZeroCode M
  | tSucc a => rawTermSuccCode M (rawQuotedTermCode M a)
  | tAdd a b => rawTermAddCode M
      (rawQuotedTermCode M a) (rawQuotedTermCode M b)
  | tMul a b => rawTermMulCode M
      (rawQuotedTermCode M a) (rawQuotedTermCode M b)
  end.

Fixpoint rawQuotedFormulaCode (M : RawPAModel) (phi : formula) : M :=
  match phi with
  | pEq a b => rawFormulaEqCode M
      (rawQuotedTermCode M a) (rawQuotedTermCode M b)
  | pBot => rawFormulaBotCode M
  | pImp a b => rawFormulaImpCode M
      (rawQuotedFormulaCode M a) (rawQuotedFormulaCode M b)
  | pAnd a b => rawFormulaAndCode M
      (rawQuotedFormulaCode M a) (rawQuotedFormulaCode M b)
  | pOr a b => rawFormulaOrCode M
      (rawQuotedFormulaCode M a) (rawQuotedFormulaCode M b)
  | pAll a => rawFormulaAllCode M (rawQuotedFormulaCode M a)
  | pEx a => rawFormulaExCode M (rawQuotedFormulaCode M a)
  end.

Arguments rawQuotedTermCode M t : clear implicits.
Arguments rawQuotedFormulaCode M phi : clear implicits.

Lemma raw_add_numeral_values_syntax : forall (M : RawPAModel),
  RawPASatisfies M -> forall m n,
  raw_add M (rawNumeralValue M m) (rawNumeralValue M n) =
  rawNumeralValue M (m + n).
Proof.
  intros M hPA m n.
  set (e := fun _ : nat => raw_zero M).
  pose proof (raw_eq_of_closed_bprov M hPA
    (tAdd (Term.numeral m) (Term.numeral n))
    (Term.numeral (m + n)) e
    (Formula.BProv_Ax_s_addNumerals nil m n)) as h.
  cbn [raw_term_eval] in h.
  rewrite !raw_term_eval_numeral in h. exact h.
Qed.

Lemma rawPolynomialPair_numerals : forall (M : RawPAModel),
  RawPASatisfies M -> forall a b,
  rawPolynomialPair M (rawNumeralValue M a) (rawNumeralValue M b) =
  rawNumeralValue M (polynomialPair a b).
Proof.
  intros M hPA a b.
  unfold rawPolynomialPair, polynomialPair.
  rewrite raw_add_numeral_values_syntax by exact hPA.
  rewrite raw_mul_numeral_values by exact hPA.
  rewrite raw_add_numeral_values_syntax by exact hPA.
  reflexivity.
Qed.

Lemma rawListNode_numerals : forall (M : RawPAModel),
  RawPASatisfies M -> forall head tail,
  rawListNode M (rawNumeralValue M head) (rawNumeralValue M tail) =
  rawNumeralValue M (S (polynomialPair head tail)).
Proof.
  intros M hPA head tail.
  unfold rawListNode. cbn [rawNumeralValue].
  f_equal. apply rawPolynomialPair_numerals. exact hPA.
Qed.

Theorem rawListCode_standard : forall (M : RawPAModel),
  RawPASatisfies M -> forall xs,
  rawListCode M (map (rawNumeralValue M) xs) =
  rawNumeralValue M (listCode xs).
Proof.
  intros M hPA xs. induction xs as [|head tail IH].
  - reflexivity.
  - cbn [map rawListCode listCode]. rewrite IH.
    apply rawListNode_numerals. exact hPA.
Qed.

Theorem rawQuotedTermCode_standard : forall (M : RawPAModel),
  RawPASatisfies M -> forall t,
  rawQuotedTermCode M t = rawNumeralValue M (termCode t).
Proof.
  intros M hPA t.
  induction t as [n | | a IHa | a IHa b IHb | a IHa b IHb];
    cbn [rawQuotedTermCode termCode rawTermVarCode rawTermZeroCode
      rawTermSuccCode rawTermAddCode rawTermMulCode
      rawCodeList1 rawCodeList2 rawCodeList3].
  - change (rawListCode M (map (rawNumeralValue M) [0; n]) =
      rawNumeralValue M (listCode [0; n])).
    apply rawListCode_standard. exact hPA.
  - change (rawListCode M (map (rawNumeralValue M) [1]) =
      rawNumeralValue M (listCode [1])).
    apply rawListCode_standard. exact hPA.
  - rewrite IHa.
    change (rawListCode M (map (rawNumeralValue M) [2; termCode a]) =
      rawNumeralValue M (listCode [2; termCode a])).
    apply rawListCode_standard. exact hPA.
  - rewrite IHa, IHb.
    change (rawListCode M
      (map (rawNumeralValue M) [3; termCode a; termCode b]) =
      rawNumeralValue M (listCode [3; termCode a; termCode b])).
    apply rawListCode_standard. exact hPA.
  - rewrite IHa, IHb.
    change (rawListCode M
      (map (rawNumeralValue M) [4; termCode a; termCode b]) =
      rawNumeralValue M (listCode [4; termCode a; termCode b])).
    apply rawListCode_standard. exact hPA.
Qed.

Theorem rawQuotedFormulaCode_standard : forall (M : RawPAModel),
  RawPASatisfies M -> forall phi,
  rawQuotedFormulaCode M phi = rawNumeralValue M (formulaCode phi).
Proof.
  intros M hPA phi.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa];
    cbn [rawQuotedFormulaCode formulaCode rawFormulaEqCode
      rawFormulaBotCode rawFormulaImpCode rawFormulaAndCode
      rawFormulaOrCode rawFormulaAllCode rawFormulaExCode
      rawCodeList1 rawCodeList2 rawCodeList3].
  - rewrite !rawQuotedTermCode_standard by exact hPA.
    change (rawListCode M
      (map (rawNumeralValue M) [0; termCode a; termCode b]) =
      rawNumeralValue M (listCode [0; termCode a; termCode b])).
    apply rawListCode_standard. exact hPA.
  - change (rawListCode M (map (rawNumeralValue M) [1]) =
      rawNumeralValue M (listCode [1])).
    apply rawListCode_standard. exact hPA.
  - rewrite IHa, IHb.
    change (rawListCode M
      (map (rawNumeralValue M) [2; formulaCode a; formulaCode b]) =
      rawNumeralValue M (listCode [2; formulaCode a; formulaCode b])).
    apply rawListCode_standard. exact hPA.
  - rewrite IHa, IHb.
    change (rawListCode M
      (map (rawNumeralValue M) [3; formulaCode a; formulaCode b]) =
      rawNumeralValue M (listCode [3; formulaCode a; formulaCode b])).
    apply rawListCode_standard. exact hPA.
  - rewrite IHa, IHb.
    change (rawListCode M
      (map (rawNumeralValue M) [4; formulaCode a; formulaCode b]) =
      rawNumeralValue M (listCode [4; formulaCode a; formulaCode b])).
    apply rawListCode_standard. exact hPA.
  - rewrite IHa.
    change (rawListCode M
      (map (rawNumeralValue M) [5; formulaCode a]) =
      rawNumeralValue M (listCode [5; formulaCode a])).
    apply rawListCode_standard. exact hPA.
  - rewrite IHa.
    change (rawListCode M
      (map (rawNumeralValue M) [6; formulaCode a]) =
      rawNumeralValue M (listCode [6; formulaCode a])).
    apply rawListCode_standard. exact hPA.
Qed.

End PABoundedRawCodedSyntaxConstructors.
