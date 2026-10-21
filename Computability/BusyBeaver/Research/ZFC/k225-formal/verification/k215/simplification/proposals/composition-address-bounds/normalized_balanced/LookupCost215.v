(** Exact constructor-visit accounting, independent of wall-clock timing.
    A branch query visits its successor row. Halt rows issue no successor query. *)
From Coq Require Import List Arith NArith.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import Prog215.
Require Import BalancedBisim NormalizedTree215.
Import ListNotations.

Definition entryCost (visit : N -> N) (x : entry) : N :=
  let '(P,_,j,k) := x in
  match tsite (ptree p215) P with
  | Some (EDecnz _,_) => (visit j + visit k)%N
  | _ => 0%N
  end.
Definition certificateCost (visit : N -> N) : N :=
  (visit 0%N + fold_right N.add 0%N
    (map (entryCost visit) (flatten NormalizedTree215)))%N.

Theorem normalized_tree_visit_count :
  certificateCost (fun j => N.of_nat (lookupDepth NormalizedTree215 j)) = 32961%N.
Proof. vm_compute. reflexivity. Qed.

Theorem normalized_list_visit_count :
  certificateCost (fun j => (j+1)%N) = 2033059%N.
Proof. vm_compute. reflexivity. Qed.

Theorem normalized_query_count : certificateCost (fun _ => 1%N) = 2851%N.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions normalized_tree_visit_count.
Print Assumptions normalized_list_visit_count.
Print Assumptions normalized_query_count.
