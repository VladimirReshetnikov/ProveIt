(** Transport for all concrete-node macro roots in current ProgLibPerm.v.
    The two imported DAG files are exact copies from the pinned repository. *)
From Coq Require Import Lists.List.
From K230 Require Import RM.
From PilotOld Require Import Dag219.
From PilotNew Require Import DagPerm.
Require Import RunTransfer.
Import ListNotations.

Definition macro_nodes : list nat :=
  [115;116;117;118;119;120;121;122;123;130;131;132;133;134;135;136;137;138;
   154;155;156;157;158;159;160;162;163;164;165;166;167;168;169;170;171;172;
   173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188;189;190;
   191;192;193;194;195;196;197;198;199;200;201;202;203;204;205;206;207;208;
   209;210;211;212;213;214;215;216;217;218;300;461;462;463;464;465;466].

Definition macro_roots : list nat :=
  [115;116;117;119;121;123;130;131;132;133;136;154;158;160;162;166;168;170;
   171;174;175;176;177;178;180;181;182;183;192;193;194;197;198;199;200;201;
   203;205;207;208;209;211;212;214;215;216;217;218;462;463;464;465;466].

Lemma macro_footprint_ok :
  check_footprint PilotOld.Dag219.dag219 PilotNew.DagPerm.dagPerm macro_nodes = true.
Proof. vm_compute. reflexivity. Qed.

Lemma macro_roots_ok : forallb (fun n => memb n macro_nodes) macro_roots = true.
Proof. vm_compute. reflexivity. Qed.

Theorem macro_run_iff n R x R' : In n macro_roots ->
  (run PilotOld.Dag219.dag219 (ENode n) R x R' <->
   run PilotNew.DagPerm.dagPerm (ENode n) R x R').
Proof.
  intro Hn. apply (run_iff _ _ macro_nodes).
  - apply check_footprint_sound, macro_footprint_ok.
  - pose proof macro_roots_ok as H.
    rewrite forallb_forall in H. specialize (H n Hn).
    apply memb_sound, H.
Qed.

(** A compatibility form for every existing total macro specification.
    No assumption about a particular input or final register file is added. *)
Theorem macro_contract n (Pre : regs -> Prop) (Post : exit -> regs -> Prop) :
  In n macro_roots ->
  (forall R, Pre R -> exists x R',
     run PilotOld.Dag219.dag219 (ENode n) R x R' /\ Post x R') ->
  forall R, Pre R -> exists x R',
     run PilotNew.DagPerm.dagPerm (ENode n) R x R' /\ Post x R'.
Proof.
  intros Hn HC R HR. destruct (HC R HR) as (x & R' & HX & HP).
  exists x, R'. split; [apply (proj1 (macro_run_iff n R x R' Hn)), HX|exact HP].
Qed.

Print Assumptions macro_run_iff.
Print Assumptions macro_contract.
