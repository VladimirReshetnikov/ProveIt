(** Exhaustive authored-proof assumption audit for the exact compact 253-state TM.
    Every authored proof is probed, including closed Box applications. *)
From M253 Require Import Table253 TM253 Zip SymExec Box Site Sites253 Check253 Boot253 Prefix Sim Main.
From M253E Require Import E2E253.

(** Fully qualified machine and shared-program endpoint; catches namespace shadowing. *)
Check (M253.Main.tm253_rm :
  M253.TM253.TM253.halts M253.TM253.tm M253.TM253.TM253.c0 <->
  M254.RM.rm_halts M254.Prog254.p254 (@nil bool, M254.Prog254.R0)).
Print M253.TM253.state.
Print M253.TM253.Ctx253.Q.
Eval cbv in M253.TM253.PNH.
Check (eq_refl : M253.TM253.PNH = 253).
Check (eq_refl : M253.TM253.Ctx253.s0 = false).
Check (eq_refl : M253.TM253.bval M253.TM253.Ctx253.q0 = 0).
Check (M253.TM253.working_rows : List.length M253.Table253.table253 = 253).
Check M253.TM253.working_rows.
Check M253.TM253.start_compact.
Check M253.TM253.halt_compact.
Check M253.Sim.site_run'.
Check M253.Sim.site_halt'.

(** Section hypotheses are explicit arguments; audit their closed applications too. *)
Print Assumptions M253.Sim.site_run'.
Print Assumptions M253.Sim.site_halt'.

(** coq/e2e/E2E253.v *)
Print Assumptions M253E.E2E253.zf253_halts_iff_SIR.
Print Assumptions M253E.E2E253.zf253_halts_iff_ZF.
Print Assumptions M253E.E2E253.zf253_halts_iff_ZFC.

(** coq/tm/Boot253.v *)
Print Assumptions M253.Boot253.prefix330_ok_true.
Print Assumptions M253.Boot253.rm_prefix330.
Print Assumptions M253.Boot253.R330_values.
Print Assumptions M253.Boot253.R330_first9.
Print Assumptions M253.Boot253.R330_physical.
Print Assumptions M253.Boot253.ext158_length.
Print Assumptions M253.Boot253.boot_regs_length.
Print Assumptions M253.Boot253.lstep_sound.
Print Assumptions M253.Boot253.lrunp_sound.
Print Assumptions M253.Boot253.dropf_spec.
Print Assumptions M253.Boot253.rev_zeros.
Print Assumptions M253.Boot253.trim_spec.
Print Assumptions M253.Boot253.boot_right_shape.
Print Assumptions M253.Boot253.boot_ok_true.
Print Assumptions M253.Boot253.boot_run.
Print Assumptions M253.Boot253.boot.
Print Assumptions M253.Boot253.boot_at_prefix330.

(** coq/tm/Box.v *)
Print Assumptions M253.Box.rev_ones.
Print Assumptions M253.Box.sepsR_app.
Print Assumptions M253.Box.sepsR_cons.
Print Assumptions M253.Box.sepsL_cons.
Print Assumptions M253.Box.sepsL_app.
Print Assumptions M253.Box.rev_sepsR.
Print Assumptions M253.Box.split_at.
Print Assumptions M253.Box.nth_split.
Print Assumptions M253.Box.incr_split.
Print Assumptions M253.Box.decr_split.
Print Assumptions M253.Box.sepsM_split.
Print Assumptions M253.Box.rev_sepsR_snoc.
Print Assumptions M253.Box.rev_sepsR_cons.
Print Assumptions M253.Box.sepsR_one.
Print Assumptions M253.Box.stR.
Print Assumptions M253.Box.stL.
Print Assumptions M253.Box.zl_c.
Print Assumptions M253.Box.zc_blank.
Print Assumptions M253.Box.zl_blank.
Print Assumptions M253.Box.fwd.
Print Assumptions M253.Box.ret.
Print Assumptions M253.Box.ret_file.
Print Assumptions M253.Box.sk_self.
Print Assumptions M253.Box.sk_next.
Print Assumptions M253.Box.skip_target_sk.
Print Assumptions M253.Box.skip.
Print Assumptions M253.Box.shift_inc.
Print Assumptions M253.Box.shift_dec_block.
Print Assumptions M253.Box.shift_dec.
Print Assumptions M253.Box.Wf_rev.
Print Assumptions M253.Box.box_mark.
Print Assumptions M253.Box.box_inc.
Print Assumptions M253.Box.zl_padr.
Print Assumptions M253.Box.sepsR_pad.
Print Assumptions M253.Box.box_dec0.
Print Assumptions M253.Box.box_decp.

(** coq/tm/Check253.v *)
Print Assumptions M253.Check253.all_leaves_check.
Print Assumptions M253.Check253.leaf_check.

(** coq/tm/Main.v *)
Print Assumptions M253.Main.inv_boot330.
Print Assumptions M253.Main.tm253_rm.
Print Assumptions M253.Main.tm253_iter.

(** coq/tm/Prefix.v *)
Print Assumptions M253.Prefix.at_halt_step_none.
Print Assumptions M253.Prefix.rm_halts_step.
Print Assumptions M253.Prefix.rm_halts_prefix.

(** coq/tm/Sim.v *)
Print Assumptions M253.Sim.vregs_length.
Print Assumptions M253.Sim.nth_vregs.
Print Assumptions M253.Sim.incr_vregs.
Print Assumptions M253.Sim.decr_vregs.
Print Assumptions M253.Sim.inc_rev_length.
Print Assumptions M253.Sim.inc_path_length.
Print Assumptions M253.Sim.strip_rev_length.
Print Assumptions M253.Sim.strip_path_length.
Print Assumptions M253.Sim.brk_length.
Print Assumptions M253.Sim.cont_length.
Print Assumptions M253.Sim.forall_false.
Print Assumptions M253.Sim.firstn_rep.
Print Assumptions M253.Sim.split_tape.
Print Assumptions M253.Sim.firstn_pad_length.
Print Assumptions M253.Sim.rm_run_snoc.
Print Assumptions M253.Sim.inv_view.
Print Assumptions M253.Sim.inv_step.
Print Assumptions M253.Sim.inv_next.
Print Assumptions M253.Sim.inv_halt.
Print Assumptions M253.Sim.reach_from.

(** coq/tm/Site.v *)
Print Assumptions M253.Site.conc_start.
Print Assumptions M253.Site.conc_target.
Print Assumptions M253.Site.run_to_sound.
Print Assumptions M253.Site.run_halt_sound.
Print Assumptions M253.Site.site_inc.
Print Assumptions M253.Site.site_dec.
Print Assumptions M253.Site.site_run.
Print Assumptions M253.Site.site_halt.

(** coq/tm/Sites253.v *)

(** coq/tm/SymExec.v *)
Print Assumptions M253.SymExec.eff_dec.
Print Assumptions M253.SymExec.boxst_dec.
Print Assumptions M253.SymExec.tok_dec.
Print Assumptions M253.SymExec.flat_cons.
Print Assumptions M253.SymExec.flat_app.
Print Assumptions M253.SymExec.flat_SB.
Print Assumptions M253.SymExec.rep_succ.
Print Assumptions M253.SymExec.sepsR_head.
Print Assumptions M253.SymExec.incr_nil.
Print Assumptions M253.SymExec.decr_nil.
Print Assumptions M253.SymExec.box_head.
Print Assumptions M253.SymExec.oracle_sound.
Print Assumptions M253.SymExec.peel_left_sound.
Print Assumptions M253.SymExec.peel_right_sound.
Print Assumptions M253.SymExec.eq_ev.
Print Assumptions M253.SymExec.step_ok_eq.
Print Assumptions M253.SymExec.step_ok_one.
Print Assumptions M253.SymExec.sstep_sound.
Print Assumptions M253.SymExec.exec_sound.
Print Assumptions M253.SymExec.flatT_push.
Print Assumptions M253.SymExec.flatT_norm.
Print Assumptions M253.SymExec.flatT_app.
Print Assumptions M253.SymExec.dropz_spec.
Print Assumptions M253.SymExec.normL_spec.
Print Assumptions M253.SymExec.toks_eqb_eq.
Print Assumptions M253.SymExec.matches_conc.

(** coq/tm/TM253.v *)
Print Assumptions M253.TM253.bnat_dec.
Print Assumptions M253.TM253.bnat_eq.
Print Assumptions M253.TM253.bval_bmk.
Print Assumptions M253.TM253.bmk_bval.
Print Assumptions M253.TM253.bval_le.
Print Assumptions M253.TM253.ball_spec.
Print Assumptions M253.TM253.compact_labels_ok.
Print Assumptions M253.TM253.compact_of_bound.
Print Assumptions M253.TM253.bval_st.
Print Assumptions M253.TM253.compact_old_of_certificate.
Print Assumptions M253.TM253.compact_old_of.
Print Assumptions M253.TM253.st_surjective.
Print Assumptions M253.TM253.Ctx253.q0_neq_q1.
Print Assumptions M253.TM253.Ctx253.s0_neq_s1.
Print Assumptions M253.TM253.Ctx253.all_syms_spec.
Print Assumptions M253.TM253.transition_eqb_eq.
Print Assumptions M253.TM253.all_labels_ok.
Print Assumptions M253.TM253.tmn_corresponds.
Print Assumptions M253.TM253.logical_table_length.
Print Assumptions M253.TM253.tmn_source_bound.
Print Assumptions M253.TM253.tm_st.
Print Assumptions M253.TM253.table_length.
Print Assumptions M253.TM253.tm_halt.
Print Assumptions M253.TM253.targets_ok.
Print Assumptions M253.TM253.start_compact.
Print Assumptions M253.TM253.halt_compact.
Print Assumptions M253.TM253.working_rows.

(** coq/tm/Table253.v *)

(** coq/tm/Zip.v *)
Print Assumptions M253.Zip.zR.
Print Assumptions M253.Zip.zL.
Print Assumptions M253.Zip.zl_cons.
Print Assumptions M253.Zip.zl_nil.
Print Assumptions M253.Zip.rep_comm.
Print Assumptions M253.Zip.rep_snoc.
Print Assumptions M253.Zip.rep_add.
Print Assumptions M253.Zip.str_app_false.
Print Assumptions M253.Zip.str_app_zeros.
Print Assumptions M253.Zip.zc_padl.
Print Assumptions M253.Zip.zl_padl.
Print Assumptions M253.Zip.zc_padr.
Print Assumptions M253.Zip.scanR.
Print Assumptions M253.Zip.scanL.

(** Read the exact final theorem types separately from their proof assumptions. *)
Set Printing All.
Check M253E.E2E253.zf253_halts_iff_SIR.
Check M253E.E2E253.zf253_halts_iff_ZF.
Check M253E.E2E253.zf253_halts_iff_ZFC.
Unset Printing All.
