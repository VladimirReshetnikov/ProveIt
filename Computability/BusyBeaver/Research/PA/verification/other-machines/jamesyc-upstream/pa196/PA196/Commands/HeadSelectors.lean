module
public import PA196.Commands.Selectors
@[expose] public section

/-! Six paper heads selected from their exact positions in the AX stack.
These symbolic proofs never evaluate the gigantic closed formula codes. -/
namespace PA196.Commands
open M6.Source.Cantor Code

theorem select_head6_total (D H A t w : Nat) :
    run (select 1 D H A) ⟨t, w, 0, 0⟩ =
      some ⟨head6 D A H, w, 0, 0⟩ := by
  unfold select
  refine append_total (m := ⟨head6 D A H, ([head4 D A H, head3 D A H, head2 D A H, head1 D H, rho8 D A H 0, U 0 0] ++ [0]).foldr pair w, 0, head5 D H⟩) ?_ ?_
  · apply append_total (discard_total t w)
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append, run, ax_step, Option.bind_some, heads,
      List.foldr_cons, List.foldr_nil, Nat.zero_add]
    simp [step, decode_pair, head1, head2, head3, head4, head5, head6, rho8, ex, N]
  · exact pops_stack [head4 D A H, head3 D A H, head2 D A H, head1 D H, rho8 D A H 0, U 0 0] (head6 D A H) 0 w 0 (head5 D H)

theorem select_head5_total (D H A t w : Nat) :
    run (select 2 D H A) ⟨t, w, 0, 0⟩ =
      some ⟨head5 D H, w, 0, 0⟩ := by
  unfold select
  refine append_total (m := ⟨head5 D H, ([head3 D A H, head2 D A H, head1 D H, rho8 D A H 0, U 0 0] ++ [0]).foldr pair w, 0, head4 D A H⟩) ?_ ?_
  · apply append_total (discard_total t w)
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append, run, ax_step, Option.bind_some, heads,
      List.foldr_cons, List.foldr_nil, Nat.zero_add]
    simp [step, decode_pair, head1, head2, head3, head4, head5, head6, rho8, ex, N]
  · exact pops_stack [head3 D A H, head2 D A H, head1 D H, rho8 D A H 0, U 0 0] (head5 D H) 0 w 0 (head4 D A H)

theorem select_head4_total (D H A t w : Nat) :
    run (select 3 D H A) ⟨t, w, 0, 0⟩ =
      some ⟨head4 D A H, w, 0, 0⟩ := by
  unfold select
  refine append_total (m := ⟨head4 D A H, ([head2 D A H, head1 D H, rho8 D A H 0, U 0 0] ++ [0]).foldr pair w, 0, head3 D A H⟩) ?_ ?_
  · apply append_total (discard_total t w)
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append, run, ax_step, Option.bind_some, heads,
      List.foldr_cons, List.foldr_nil, Nat.zero_add]
    simp [step, decode_pair, head1, head2, head3, head4, head5, head6, rho8, ex, N]
  · exact pops_stack [head2 D A H, head1 D H, rho8 D A H 0, U 0 0] (head4 D A H) 0 w 0 (head3 D A H)

theorem select_head3_total (D H A t w : Nat) :
    run (select 4 D H A) ⟨t, w, 0, 0⟩ =
      some ⟨head3 D A H, w, 0, 0⟩ := by
  unfold select
  refine append_total (m := ⟨head3 D A H, ([head1 D H, rho8 D A H 0, U 0 0] ++ [0]).foldr pair w, 0, head2 D A H⟩) ?_ ?_
  · apply append_total (discard_total t w)
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append, run, ax_step, Option.bind_some, heads,
      List.foldr_cons, List.foldr_nil, Nat.zero_add]
    simp [step, decode_pair, head1, head2, head3, head4, head5, head6, rho8, ex, N]
  · exact pops_stack [head1 D H, rho8 D A H 0, U 0 0] (head3 D A H) 0 w 0 (head2 D A H)

theorem select_head2_total (D H A t w : Nat) :
    run (select 5 D H A) ⟨t, w, 0, 0⟩ =
      some ⟨head2 D A H, w, 0, 0⟩ := by
  unfold select
  refine append_total (m := ⟨head2 D A H, ([rho8 D A H 0, U 0 0] ++ [0]).foldr pair w, 0, head1 D H⟩) ?_ ?_
  · apply append_total (discard_total t w)
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append, run, ax_step, Option.bind_some, heads,
      List.foldr_cons, List.foldr_nil, Nat.zero_add]
    simp [step, decode_pair, head1, head2, head3, head4, head5, head6, rho8, ex, N]
  · exact pops_stack [rho8 D A H 0, U 0 0] (head2 D A H) 0 w 0 (head1 D H)

theorem select_head1_total (D H A t w : Nat) :
    run (select 6 D H A) ⟨t, w, 0, 0⟩ =
      some ⟨head1 D H, w, 0, 0⟩ := by
  unfold select
  refine append_total (m := ⟨head1 D H, ([U 0 0] ++ [0]).foldr pair w, 0, rho8 D A H 0⟩) ?_ ?_
  · apply append_total (discard_total t w)
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append, run, ax_step, Option.bind_some, heads,
      List.foldr_cons, List.foldr_nil, Nat.zero_add]
    simp [step, decode_pair, head1, head2, head3, head4, head5, head6, rho8, ex, N]
  · exact pops_stack [U 0 0] (head1 D H) 0 w 0 (rho8 D A H 0)

#print axioms select_head1_total
#print axioms select_head2_total
#print axioms select_head3_total
#print axioms select_head4_total
#print axioms select_head5_total
#print axioms select_head6_total
end PA196.Commands
