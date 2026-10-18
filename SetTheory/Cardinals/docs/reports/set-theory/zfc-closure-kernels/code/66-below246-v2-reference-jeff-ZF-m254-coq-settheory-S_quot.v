(** * S_quot: the bisimulation quotient inside S0

    Ordered pairs are Kuratowski codes [OP0 x y c] (Z_base: c has a member with exact singleton
    profile {x}, a member with exact pair profile {x,y}, and no other members).  A raw set [R]
    codes the relation [App0 R x y] := ∃c∈R. OP0 x y c.  There may be many codes of one pair;
    only endpoint uniqueness ([op_inj]) is needed.

      Bisim R  :=  every R-edge (p,q) satisfies forth (∀a∈p ∃b∈q. R a b) and back (∀b∈q ∃a∈p. R a b)
      Eqv x y  :=  ∃R. Bisim R ∧ R x y                       (interpreted equality, "≈")
      Mem x y  :=  ∃u∈y. Eqv x u                              (interpreted membership, "E*")

    [qtS] = [qt Eqv Mem] translates ZF formulas into S.

    Proved here: ≈ is an equivalence ([eqv_refl], [eqv_sym], [eqv_trans]), Mem respects it
    ([mem_l], [mem_r]), quotient extensionality ([eqv_ext]) and formula invariance ([qt_inv]).
    [Sq] lists the fixed GIC closures used (S_raw's and five more). *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From ZFC Require Import Z_rel Z_base.
From M254S Require Import S_def S_qt S_gic S_raw.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
#[local] Set Default Proof Using "All".

(** ** Definitions *)
Definition Bisim (R : term) : form :=
  ∀ (∀ (App0 R`[↑]`[↑] $1 $0 →
       (∀ ($0 ∈' $2 → ∃ ($0 ∈' $2 ∧ App0 R`[↑]`[↑]`[↑]`[↑] $1 $0))) ∧
       (∀ ($0 ∈' $1 → ∃ ($0 ∈' $3 ∧ App0 R`[↑]`[↑]`[↑]`[↑] $0 $1))))).
Definition Eqv (x y : term) : form := ∃ (Bisim $0 ∧ App0 $0 x`[↑] y`[↑]).
Definition Mem (x y : term) : form := ∃ ($0 ∈' y`[↑] ∧ Eqv x`[↑] $0).

#[global] Arguments Bisim : simpl never.
#[global] Arguments Eqv : simpl never.
#[global] Arguments Mem : simpl never.

Lemma Bisim_subst R sg : (Bisim R)[sg] = Bisim R`[sg].
Proof. psubst Bisim. Qed.
#[global] Hint Rewrite Bisim_subst : fsub.
Lemma Eqv_subst x y sg : (Eqv x y)[sg] = Eqv x`[sg] y`[sg].
Proof. psubst Eqv. Qed.
#[global] Hint Rewrite Eqv_subst : fsub.
Lemma Mem_subst x y sg : (Mem x y)[sg] = Mem x`[sg] y`[sg].
Proof. psubst Mem. Qed.
#[global] Hint Rewrite Mem_subst : fsub.

Definition qtS {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : form := qt Eqv Mem phi.

Lemma qtS_subst (phi : form) sg : (qtS phi)[sg] = qtS (phi[sg]).
Proof. apply qt_subst; [exact Eqv_subst | exact Mem_subst]. Qed.

(** ** The fixed GIC closures used by the quotient *)
(** diagonal codes over V ($1): ∃t∈V. OP0 t t c *)
Definition psi_diag : form := ∃ ($0 ∈' $2 ∧ OP0 $0 $0 $1).
(** reversed codes of R ($1): ∃p q. App0 R p q ∧ OP0 q p c *)
Definition psi_rev : form := ∃ (∃ (App0 $3 $1 $0 ∧ OP0 $0 $1 $2)).
(** composite codes of R1 ($1), R2 ($2): ∃s t u. App0 R1 s t ∧ App0 R2 t u ∧ OP0 s u c *)
Definition psi_comp : form := ∃ (∃ (∃ ((App0 $4 $2 $1 ∧ App0 $5 $1 $0) ∧ OP0 $2 $0 $3))).
(** collecting bisimulations: input u ($0), output R ($1), parameter y / x ($2) *)
Definition th_extF : form := ∃ ($0 ∈' $3 ∧ (Bisim $2 ∧ App0 $2 $1 $0)).
Definition th_extB : form := ∃ ($0 ∈' $3 ∧ (Bisim $2 ∧ App0 $2 $0 $1)).

Definition Sq_quot : list form :=
  [forall_times 2 (gic (sep_th psi_diag)); forall_times 2 (gic (sep_th psi_rev));
   forall_times 3 (gic (sep_th psi_comp)); forall_times 1 (gic th_extF); forall_times 1 (gic th_extB)].

Definition Sq : list form := Sq_raw ++ Sq_quot.

Ltac fb_solve := unfold psi_diag, psi_rev, psi_comp, th_extF, th_extB, Bisim, App0, OP0, Sing0, Pair0; cbn; lia.

Lemma Sq_ok a : In a Sq -> S0 a.
Proof.
  intros H. apply in_app_or in H as [H|H]; [now apply Sq_raw_ok|].
  destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; apply S0_gic, gic_closed.
  - apply (fb_sep_th 1). fb_solve.
  - apply (fb_sep_th 1). fb_solve.
  - apply (fb_sep_th 2). fb_solve.
  - fb_solve.
  - fb_solve.
Qed.

Lemma Sq_raw_of {G} : incl Sq G -> incl Sq_raw G.
Proof. intros H a Ha. apply H, in_or_app. now left. Qed.

Lemma HE {G} (HB : incl Sbase G) : incl EqAx G.
Proof. intros a Ha. apply HB. cbn in *. tauto. Qed.

(** *** The quotient *)

(** diagonal codes over a CP container *)
Lemma eqv_refl {G} (HB : incl Sbase G) (HQ : incl Sq G) x : G ⊢C Eqv x x.
Proof.
  pose proof (HE HB) as HE. pose proof (Sq_raw_of HQ) as HR.
  fobtain (cp_ex HB x) as V HV0. fdestr HV0 HxV HV.
  fobtain (codes_ex HB V) as D HD.
  pose proof (HQ (forall_times 2 (gic (sep_th psi_diag))) ltac:(cbn; tauto)) as Hin.
  pose proof (sepS_use _ 1 psi_diag (V .: var) D HE Hin ltac:(fb_solve)) as T.
  fex T R HRd. unfold psi_diag in HRd. simp_in HRd.
  fassert Hdiag : (∀ ($0 ∈' V`[↑] → App0 R`[↑] $0 $0)).
  { fall a. fintro Ha. fobtain (op_ex HB HR a a) as c Hc.
    unfold App0. fexists c. fsplit; [|exact Hc]. finst HRd c. apply (iff_r _ _ _ HRd). fsplit.
    - finst HD a. fmp HD Ha. finst HD a. fmp HD Ha. finst HD c. exact (IE HD Hc).
    - fexists a. fsplit; [exact Ha | exact Hc]. }
  unfold Eqv. fexists R. fsplit.
  - unfold Bisim. fall p. fall q. fintro Hpq.
    fassert Hk : (p ≡' q ∧ p ∈' V).
    { unfold App0 in Hpq. fex Hpq c Hc. fdestr Hc HcR Hcop. finst HRd c.
      fhave T : (iff_l _ _ _ HRd HcR). fdestr T T1 T2. fex T2 t Ht. fdestr Ht HtV Htop.
      fhave E : (op_inj HE p q t t c Hcop Htop). fdestr E E1 E2. fsplit; [feqE | fmemE]. }
    fdestr Hk Hpq' HpV. fsplit.
    + fall a. fintro Ha. fexists a. fsplit; [fmemE|].
      finst Hdiag a. apply (IE Hdiag). exact (cp_trans V p a HV HpV Ha).
    + fall b. fintro Hb. fexists b. fsplit; [fmemE|].
      finst Hdiag b. apply (IE Hdiag). apply (cp_trans V p b HV HpV). fmemE.
  - finst Hdiag x. exact (IE Hdiag HxV).
Qed.

(** using a bisimulation at an edge *)
Lemma bis_forth {G} R p q a : G ⊢C Bisim R -> G ⊢C App0 R p q -> G ⊢C a ∈' p ->
  G ⊢C ∃ ($0 ∈' q`[↑] ∧ App0 R`[↑] a`[↑] $0).
Proof.
  intros H Hpq Ha. unfold Bisim in H. finst H p q. fmp H Hpq. fdestr H H1 H2. finst H1 a. exact (IE H1 Ha).
Qed.

Lemma bis_back {G} R p q b : G ⊢C Bisim R -> G ⊢C App0 R p q -> G ⊢C b ∈' q ->
  G ⊢C ∃ ($0 ∈' p`[↑] ∧ App0 R`[↑] $0 b`[↑]).
Proof.
  intros H Hpq Hb. unfold Bisim in H. finst H p q. fmp H Hpq. fdestr H H1 H2. finst H2 b. exact (IE H2 Hb).
Qed.

(** reversed codes *)
Lemma eqv_sym {G} (HB : incl Sbase G) (HQ : incl Sq G) x y : G ⊢C Eqv x y -> G ⊢C Eqv y x.
Proof.
  intros H. pose proof (HE HB) as HE. pose proof (Sq_raw_of HQ) as HR.
  unfold Eqv in H. fex H R HR0. fdestr HR0 HBis Hxy.
  fobtain (cp_ex HB R) as V HV0. fdestr HV0 HRV HV.
  fobtain (codes_ex HB V) as D HD.
  pose proof (HQ (forall_times 2 (gic (sep_th psi_rev))) ltac:(cbn; tauto)) as Hin.
  pose proof (sepS_use _ 1 psi_rev (R .: var) D HE Hin ltac:(fb_solve)) as T.
  fex T R' HR'. unfold psi_rev in HR'. simp_in HR'.
  fassert Hrev : (∀ (∀ (App0 R`[↑]`[↑] $1 $0 → App0 R'`[↑]`[↑] $0 $1))).
  { fall p. fall q. fintro Hpq. fhave Hin2 : (app_in V R p q HV HRV Hpq). fdestr Hin2 HpV HqV.
    fobtain (op_ex HB HR q p) as c Hc. unfold App0. fexists c. fsplit; [|exact Hc].
    finst HR' c. apply (iff_r _ _ _ HR'). fsplit.
    - finst HD q. fmp HD HqV. finst HD p. fmp HD HpV. finst HD c. exact (IE HD Hc).
    - fexists p. fexists q. fsplit; [exact Hpq | exact Hc]. }
  unfold Eqv. fexists R'. fsplit.
  - unfold Bisim. fall u. fall w. fintro Huw.
    fassert Hk : (∃ (∃ (App0 R`[↑]`[↑] $1 $0 ∧ (u`[↑]`[↑] ≡' $0 ∧ w`[↑]`[↑] ≡' $1)))).
    { unfold App0 in Huw. fex Huw c Hc. fdestr Hc HcR Hcop. finst HR' c.
      fhave T : (iff_l _ _ _ HR' HcR). fdestr T T1 T2. fex T2 p Hp. fex Hp q Hq. fdestr Hq Hq1 Hq2.
      fhave E : (op_inj HE u w q p c Hcop Hq2). fdestr E E1 E2.
      fexists p. fexists q. fsplit; [exact Hq1 | fsplit; [exact E1 | exact E2]]. }
    fex Hk p Hp. fex Hp q Hq. fdestr Hq Hpq Heq. fdestr Heq Euq Ewp. fsplit.
    + fall m. fintro Hm. fassert Hmq : (m ∈' q); [fmemE|].
      fhave T : (bis_back R p q m HBis Hpq Hmq). fex T n Hn. fdestr Hn Hnp Hnm.
      fexists n. fsplit; [fmemE|]. finst Hrev n m. exact (IE Hrev Hnm).
    + fall n. fintro Hn. fassert Hnp : (n ∈' p); [fmemE|].
      fhave T : (bis_forth R p q n HBis Hpq Hnp). fex T m Hm. fdestr Hm Hmq Hnm.
      fexists m. fsplit; [fmemE|]. finst Hrev n m. exact (IE Hrev Hnm).
  - finst Hrev x y. exact (IE Hrev Hxy).
Qed.

(** composite codes, separated from an all-code bound *)
Lemma eqv_trans {G} (HB : incl Sbase G) (HQ : incl Sq G) x y z : G ⊢C Eqv x y -> G ⊢C Eqv y z -> G ⊢C Eqv x z.
Proof.
  intros H1 H2. pose proof (HE HB) as HE. pose proof (Sq_raw_of HQ) as HR.
  unfold Eqv in H1, H2. fex H1 R1 HR1. fdestr HR1 HB1 Hxy. fex H2 R2 HR2. fdestr HR2 HB2 Hyz.
  fobtain (pair_ex HB HR R1 R2) as P HP.
  fobtain (cp_ex HB P) as V HV0. fdestr HV0 HPV HV.
  fhave HR1V : (cp_trans V P R1 HV HPV (pair0_inl HE R1 R2 P HP)).
  fhave HR2V : (cp_trans V P R2 HV HPV (pair0_inr HE R1 R2 P HP)).
  fobtain (codes_ex HB V) as D HD.
  pose proof (HQ (forall_times 3 (gic (sep_th psi_comp))) ltac:(cbn; tauto)) as Hin.
  pose proof (sepS_use _ 2 psi_comp (R1 .: R2 .: var) D HE Hin ltac:(fb_solve)) as T.
  fex T R HRc. unfold psi_comp in HRc. simp_in HRc.
  fassert Hcomp : (∀ (∀ (∀ (App0 R1`[↑]`[↑]`[↑] $2 $1 → App0 R2`[↑]`[↑]`[↑] $1 $0 → App0 R`[↑]`[↑]`[↑] $2 $0)))).
  { fall s. fall t. fall u. fintro Hst. fintro Htu.
    fhave Hs : (app_in V R1 s t HV HR1V Hst). fdestr Hs HsV HtV.
    fhave Hu : (app_in V R2 t u HV HR2V Htu). fdestr Hu HtV' HuV.
    fobtain (op_ex HB HR s u) as c Hc. unfold App0. fexists c. fsplit; [|exact Hc].
    finst HRc c. apply (iff_r _ _ _ HRc). fsplit.
    - finst HD s. fmp HD HsV. finst HD u. fmp HD HuV. finst HD c. exact (IE HD Hc).
    - fexists s. fexists t. fexists u. fsplit; [fsplit; [exact Hst | exact Htu] | exact Hc]. }
  unfold Eqv. fexists R. fsplit.
  - unfold Bisim. fall s'. fall u'. fintro Hsu.
    fassert Hk : (∃ (∃ (∃ ((App0 R1`[↑]`[↑]`[↑] $2 $1 ∧ App0 R2`[↑]`[↑]`[↑] $1 $0) ∧
                          (s'`[↑]`[↑]`[↑] ≡' $2 ∧ u'`[↑]`[↑]`[↑] ≡' $0))))).
    { unfold App0 in Hsu. fex Hsu c Hc. fdestr Hc HcR Hcop. finst HRc c.
      fhave T : (iff_l _ _ _ HRc HcR). fdestr T T1 T2. fex T2 s Hs. fex Hs t Ht. fex Ht u Hu.
      fdestr Hu Hu1 Hu2. fhave E : (op_inj HE s' u' s u c Hcop Hu2). fdestr E E1 E2.
      fexists s. fexists t. fexists u. fsplit; [exact Hu1 | fsplit; [exact E1 | exact E2]]. }
    fex Hk s Hs. fex Hs t Ht. fex Ht u Hu. fdestr Hu Hu1 Heq. fdestr Hu1 Hst Htu. fdestr Heq Es Eu.
    fsplit.
    + fall a. fintro Ha. fassert Has : (a ∈' s); [fmemE|].
      fhave T : (bis_forth R1 s t a HB1 Hst Has). fex T b Hb. fdestr Hb Hbt Hab.
      fhave T : (bis_forth R2 t u b HB2 Htu Hbt). fex T d Hd. fdestr Hd Hdu Hbd.
      fexists d. fsplit; [fmemE|]. finst Hcomp a b d. fmp Hcomp Hab. exact (IE Hcomp Hbd).
    + fall d. fintro Hd. fassert Hdu : (d ∈' u); [fmemE|].
      fhave T : (bis_back R2 t u d HB2 Htu Hdu). fex T b Hb. fdestr Hb Hbt Hbd.
      fhave T : (bis_back R1 s t b HB1 Hst Hbt). fex T a Ha. fdestr Ha Has Hab.
      fexists a. fsplit; [fmemE|]. finst Hcomp a b d. fmp Hcomp Hab. exact (IE Hcomp Hbd).
  - finst Hcomp x y z. fmp Hcomp Hxy. exact (IE Hcomp Hyz).
Qed.

Lemma eqv_of_eq {G} (HB : incl Sbase G) (HQ : incl Sq G) x y : G ⊢C x ≡' y -> G ⊢C Eqv x y.
Proof.
  intros H. pose proof (eqv_refl HB HQ x) as H0.
  pose proof (leibE G (Eqv x`[↑] $0) x y (HE HB) H) as T. simp_in T. exact (T H0).
Qed.

(** forth clause at the root edge, then transitivity *)
Lemma mem_r {G} (HB : incl Sbase G) (HQ : incl Sq G) x y y' : G ⊢C Eqv y y' -> G ⊢C Mem x y -> G ⊢C Mem x y'.
Proof.
  intros H1 H2. unfold Eqv in H1. fex H1 R HR0. fdestr HR0 HBis Hyy.
  unfold Mem in H2. fex H2 u Hu. fdestr Hu Huy Hxu.
  fhave T : (bis_forth R y y' u HBis Hyy Huy). fex T b Hb. fdestr Hb Hby Hub.
  unfold Mem. fexists b. fsplit; [exact Hby|]. apply (eqv_trans HB HQ _ u _ Hxu).
  unfold Eqv. fexists R. fsplit; [exact HBis | exact Hub].
Qed.

Lemma mem_l {G} (HB : incl Sbase G) (HQ : incl Sq G) x x' y : G ⊢C Eqv x x' -> G ⊢C Mem x y -> G ⊢C Mem x' y.
Proof.
  intros H1 H2. unfold Mem in *. fex H2 u Hu. fdestr Hu Hu1 Hu2. fexists u. fsplit; [exact Hu1|].
  apply (eqv_trans HB HQ _ x); [apply (eqv_sym HB HQ)|]; assumption.
Qed.

Lemma mem_raw {G} (HB : incl Sbase G) (HQ : incl Sq G) x y : G ⊢C x ∈' y -> G ⊢C Mem x y.
Proof. intros H. unfold Mem. fexists x. fsplit; [exact H | apply (eqv_refl HB HQ)]. Qed.

(** helpers for the union construction *)
Lemma union0_in {G} X U w c : G ⊢C Union0 X U -> G ⊢C w ∈' X -> G ⊢C c ∈' w -> G ⊢C c ∈' U.
Proof. intros H Hw Hc. unfold Union0 in H. fdestr H H1 H2. finst H2 w. fmp H2 Hw. finst H2 c. exact (IE H2 Hc). Qed.

Lemma union0_el {G} X U c : G ⊢C Union0 X U -> G ⊢C c ∈' U -> G ⊢C ∃ ($0 ∈' X`[↑] ∧ c`[↑] ∈' $0).
Proof. intros H Hc. unfold Union0 in H. fdestr H H1 H2. finst H1 c. exact (IE H1 Hc). Qed.

Lemma app_sub {G} r R a b : G ⊢C ∀ ($0 ∈' r`[↑] → $0 ∈' R`[↑]) -> G ⊢C App0 r a b -> G ⊢C App0 R a b.
Proof.
  intros Hs H. unfold App0 in *. fex H c Hc. fdestr Hc Hcr Hop. fexists c. fsplit; [|exact Hop].
  finst Hs c. exact (IE Hs Hcr).
Qed.

(** a bisimulation r contained in R gives R's forth/back clauses at r's edges *)
Lemma bis_sub {G} r R p q : G ⊢C Bisim r -> G ⊢C ∀ ($0 ∈' r`[↑] → $0 ∈' R`[↑]) -> G ⊢C App0 r p q ->
  G ⊢C (∀ ($0 ∈' p`[↑] → ∃ ($0 ∈' q`[↑]`[↑] ∧ App0 R`[↑]`[↑] $1 $0))) ∧
       (∀ ($0 ∈' q`[↑] → ∃ ($0 ∈' p`[↑]`[↑] ∧ App0 R`[↑]`[↑] $0 $1))).
Proof.
  intros Hb Hs Hpq. fsplit.
  - fall a. fintro Ha. fhave T : (bis_forth r p q a Hb Hpq Ha). fex T b Hb'. fdestr Hb' Hbq Hab.
    fexists b. fsplit; [exact Hbq | exact (app_sub r R a b Hs Hab)].
  - fall b. fintro Hb'. fhave T : (bis_back r p q b Hb Hpq Hb'). fex T a Ha. fdestr Ha Hap Hab.
    fexists a. fsplit; [exact Hap | exact (app_sub r R a b Hs Hab)].
Qed.

(** quotient extensionality: collect, with two GIC instances, whole local bisimulations for the
    children of x and of y, and take their union plus one code of (x,y) *)
Lemma eqv_ext {G} (HB : incl Sbase G) (HQ : incl Sq G) x y : G ⊢C ∀ (Mem $0 x`[↑] → Mem $0 y`[↑]) -> G ⊢C ∀ (Mem $0 y`[↑] → Mem $0 x`[↑]) ->
  G ⊢C Eqv x y.
Proof.
  intros Hxy Hyx. pose proof (HE HB) as HE. pose proof (Sq_raw_of HQ) as HR.
  (* root matching *)
  fassert Hf : (∀ ($0 ∈' x`[↑] → ∃ ($0 ∈' y`[↑]`[↑] ∧ Eqv $1 $0))).
  { fall a. fintro Ha. finst Hxy a. fmp Hxy (mem_raw HB HQ a x Ha). unfold Mem in Hxy. exact Hxy. }
  fassert Hb : (∀ ($0 ∈' y`[↑] → ∃ ($0 ∈' x`[↑]`[↑] ∧ Eqv $0 $1))).
  { fall b. fintro Hb. finst Hyx b. fmp Hyx (mem_raw HB HQ b y Hb). unfold Mem in Hyx.
    fex Hyx a Ha. fdestr Ha Hax Hba. fexists a. fsplit; [exact Hax | exact (eqv_sym HB HQ _ _ Hba)]. }
  (* the two collections *)
  pose proof (HQ (forall_times 1 (gic th_extF)) ltac:(cbn; tauto)) as HinF.
  pose proof (gic_use _ 1 th_extF (y .: var) x HinF ltac:(fb_solve)) as T.
  fex T Fc HFc. fdestr HFc HcovF HnxF. unfold th_extF in HcovF, HnxF. simp_in HcovF. simp_in HnxF.
  pose proof (HQ (forall_times 1 (gic th_extB)) ltac:(cbn; tauto)) as HinB.
  pose proof (gic_use _ 1 th_extB (x .: var) y HinB ltac:(fb_solve)) as T.
  fex T Gc HGc. fdestr HGc HcovB HnxB. unfold th_extB in HcovB, HnxB. simp_in HcovB. simp_in HnxB.
  (* R := ⋃{⋃{⋃F, ⋃Gc}, {k}} *)
  fobtain (union_ex HB HR Fc) as U1 HU1. fobtain (union_ex HB HR Gc) as U2 HU2.
  fobtain (pair_ex HB HR U1 U2) as P1 HP1. fobtain (union_ex HB HR P1) as U12 HU12.
  fobtain (op_ex HB HR x y) as k Hk. fobtain (pair_ex HB HR k k) as Pk HPk.
  fobtain (pair_ex HB HR U12 Pk) as P2 HP2. fobtain (union_ex HB HR P2) as R HRu.
  fassert HsubF : (∀ ($0 ∈' Fc`[↑] → ∀ ($0 ∈' $1 → $0 ∈' R`[↑]`[↑]))).
  { fall r. fintro Hr. fall c. fintro Hc. apply (union0_in P2 R U12 c HRu (pair0_inl HE U12 Pk P2 HP2)).
    apply (union0_in P1 U12 U1 c HU12 (pair0_inl HE U1 U2 P1 HP1)). exact (union0_in Fc U1 r c HU1 Hr Hc). }
  fassert HsubB : (∀ ($0 ∈' Gc`[↑] → ∀ ($0 ∈' $1 → $0 ∈' R`[↑]`[↑]))).
  { fall r. fintro Hr. fall c. fintro Hc. apply (union0_in P2 R U12 c HRu (pair0_inl HE U12 Pk P2 HP2)).
    apply (union0_in P1 U12 U2 c HU12 (pair0_inr HE U1 U2 P1 HP1)). exact (union0_in Gc U2 r c HU2 Hr Hc). }
  fassert HkR : (k ∈' R).
  { exact (union0_in P2 R Pk k HRu (pair0_inr HE U12 Pk P2 HP2) (pair0_inl HE k k Pk HPk)). }
  fassert Hcases : (∀ ($0 ∈' R`[↑] → $0 ≡' k`[↑] ∨ ((∃ ($0 ∈' Fc`[↑]`[↑] ∧ $1 ∈' $0)) ∨ (∃ ($0 ∈' Gc`[↑]`[↑] ∧ $1 ∈' $0))))).
  { fall c. fintro Hc. fhave T : (union0_el P2 R c HRu Hc). fex T w Hw. fdestr Hw HwP Hcw.
    fhave E : (pair0_el HE U12 Pk P2 w HP2 HwP). fcases E E1 E2.
    - fright. fassert Hc12 : (c ∈' U12); [fmemE|].
      fhave T : (union0_el P1 U12 c HU12 Hc12). fex T w' Hw'. fdestr Hw' Hw'P Hcw'.
      fhave E : (pair0_el HE U1 U2 P1 w' HP1 Hw'P). fcases E E3 E4.
      + fleft. fassert Hc1 : (c ∈' U1); [fmemE|]. exact (union0_el Fc U1 c HU1 Hc1).
      + fright. fassert Hc2 : (c ∈' U2); [fmemE|]. exact (union0_el Gc U2 c HU2 Hc2).
    - fleft. fassert Hck : (c ∈' Pk); [fmemE|]. fhave E : (pair0_el HE k k Pk c HPk Hck).
      fcases E E3 E4; [exact E3 | exact E4]. }
  unfold Eqv. fexists R. fsplit.
  - unfold Bisim. fall p. fall q. fintro Hpq. pose proof Hpq as Hpq'. unfold App0 in Hpq'.
    fex Hpq' c Hc. fdestr Hc HcR Hcop. finst Hcases c. fmp Hcases HcR. fcases Hcases C1 C2.
    + (* the root code *)
      frewE_in C1 (OP0 p`[↑] q`[↑] $0) Hcop.
      fhave E : (op_inj HE p q x y k Hcop Hk). fdestr E Epx Eqy. fsplit.
      * fall a. fintro Ha. fassert Hax : (a ∈' x); [fmemE|].
        pose proof Hf as T. finst T a. fmp T Hax. fex T b Hb'. fdestr Hb' Hby Hab.
        unfold Eqv in Hab. fex Hab R0 HR0. fdestr HR0 HB0 Hab0.
        pose proof HcovF as T. finst T a. fmp T Hax. finst T R0.
        fassert A : (∃ ($0 ∈' y`[↑] ∧ (Bisim R0`[↑] ∧ App0 R0`[↑] a`[↑] $0))).
        { fexists b. fsplit; [exact Hby | fsplit; [exact HB0 | exact Hab0]]. }
        fmp T A. fex T r Hr. fdestr Hr Hr1 HrF. fex Hr1 v Hv. fdestr Hv Hvy Hv2. fdestr Hv2 Hbr Har.
        fexists v. fsplit; [fmemE|]. apply (app_sub r R a v); [|exact Har].
        finst HsubF r. exact (IE HsubF HrF).
      * fall b. fintro Hb'. fassert Hby : (b ∈' y); [fmemE|].
        pose proof Hb as T. finst T b. fmp T Hby. fex T a Ha. fdestr Ha Hax Hab.
        unfold Eqv in Hab. fex Hab R0 HR0. fdestr HR0 HB0 Hab0.
        pose proof HcovB as T. finst T b. fmp T Hby. finst T R0.
        fassert A : (∃ ($0 ∈' x`[↑] ∧ (Bisim R0`[↑] ∧ App0 R0`[↑] $0 b`[↑]))).
        { fexists a. fsplit; [exact Hax | fsplit; [exact HB0 | exact Hab0]]. }
        fmp T A. fex T r Hr. fdestr Hr Hr1 HrB. fex Hr1 u Hu. fdestr Hu Hux Hu2. fdestr Hu2 Hbr Hub.
        fexists u. fsplit; [fmemE|]. apply (app_sub r R u b); [|exact Hub].
        finst HsubB r. exact (IE HsubB HrB).
    + fcases C2 C3 C4.
      * fex C3 r Hr. fdestr Hr HrF Hcr. finst HnxF r. fmp HnxF HrF. fex HnxF u Hu. fex Hu v Hv.
        fdestr Hv Hvy Hv2. fdestr Hv2 Hbr Huv.
        apply (bis_sub r R p q Hbr).
        -- finst HsubF r. exact (IE HsubF HrF).
        -- unfold App0. fexists c. fsplit; [exact Hcr | exact Hcop].
      * fex C4 r Hr. fdestr Hr HrB Hcr. finst HnxB r. fmp HnxB HrB. fex HnxB v Hv. fex Hv u Hu.
        fdestr Hu Hux Hu2. fdestr Hu2 Hbr Huv.
        apply (bis_sub r R p q Hbr).
        -- finst HsubB r. exact (IE HsubB HrB).
        -- unfold App0. fexists c. fsplit; [exact Hcr | exact Hcop].
  - unfold App0. fexists k. fsplit; [exact HkR | exact Hk].
Qed.


(** ** Formula invariance (proved from the congruence lemmas) *)
Lemma qt_inv (phi : form) : forall G (sg tau : nat -> term), incl Sbase G -> incl Sq G ->
  (forall n, G ⊢C Eqv (sg n) (tau n)) -> G ⊢C (qtS phi)[sg] -> G ⊢C (qtS phi)[tau].
Proof.
  induction phi as [| P v | op a IHa b IHb | q a IHa] using form_ind_falsity;
    intros G sg tau HG HQ Hst H.
  - exact H.
  - unfold qtS in *. destruct P; cbn in v |- *; rewrite (vec2 v) in H |- *; cbn in *;
      rewrite ?Eqv_subst, ?Mem_subst in *;
      destruct (Vector.hd v) as [n|[]]; destruct (Vector.hd (Vector.tl v)) as [m|[]]; cbn in *.
    + eapply mem_l; [exact HG|exact HQ|apply Hst|]. eapply mem_r; [exact HG|exact HQ|apply Hst|exact H].
    + eapply eqv_trans; [exact HG|exact HQ| |]. apply eqv_sym; [exact HG|exact HQ|]. apply Hst.
      eapply eqv_trans; [exact HG|exact HQ|exact H|apply Hst].
  - assert (Hts : forall n, G ⊢C Eqv (tau n) (sg n)) by (intros n; apply eqv_sym; auto).
    unfold qtS in *. destruct op; cbn in H |- *.
    + apply CI; [eapply IHa|eapply IHb]; eauto; [eapply CE1|eapply CE2]; exact H.
    + apply (DE H).
      * apply DI1. eapply IHa; [now apply incl_cons_r|now apply incl_cons_r| |apply Ctx; now left].
        intros n. apply weak_cons, Hst.
      * apply DI2. eapply IHb; [now apply incl_cons_r|now apply incl_cons_r| |apply Ctx; now left].
        intros n. apply weak_cons, Hst.
    + apply II. eapply IHb; [now apply incl_cons_r|now apply incl_cons_r| intros n; apply weak_cons, Hst|].
      eapply IE; [apply weak_cons, H|].
      eapply IHa; [now apply incl_cons_r|now apply incl_cons_r| intros n; apply weak_cons, Hts|].
      apply Ctx; now left.
  - unfold qtS in *. destruct q; cbn in H |- *.
    + apply AllI_named. intros t. apply (AllE t) in H. rewrite up_inst_form in H |- *.
      eapply IHa; [exact HG|exact HQ| |exact H]. intros [|n]; cbn; [now apply eqv_refl|]. apply Hst.
    + apply (ExE_named H). intros t. rewrite up_inst_form. apply (ExI t). rewrite up_inst_form.
      eapply IHa; [now apply incl_cons_r|now apply incl_cons_r| |apply Ctx; now left].
      intros [|n]; cbn; [apply eqv_refl; now apply incl_cons_r|]. apply weak_cons, Hst.
Qed.
