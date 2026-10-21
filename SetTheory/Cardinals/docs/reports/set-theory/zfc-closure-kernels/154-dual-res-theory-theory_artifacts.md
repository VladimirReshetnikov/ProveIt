# Theory-side artifact guide

`theory_results.tex` is the report include. It has no preamble and requires
the ordinary `amsmath` and `amssymb` packages. Its section labels are stable;
in particular the overview can link to `sec:new-theory`.

The complete arguments are in the include and these expanded notes:

- `negative_equality_dual_b.md`: negative equality plus the dual quantifier
  row, with the exact full-rho1 and original odd-tag restrictions.
- `disequality_codec.md`: negative equality with the original rho6,
  compact rho1, and parity halting.
- `membership_blind_detachment.md`: inverse inference with arbitrary
  membership decoding, the approximate arithmetic decoder, and the
  corollary allowing both odd tags to decode arbitrarily under disequality.
- `shifted_even_codec.md`: a directly calibrated even-tag shift that
  matches the eleven-leaf approximate decoder exactly on both required
  constructors, with a benign double interpretation of zero as truth.
- `forward_mp_conventions.md`: complete command-block proofs for the three
  altered successful MP returns, including the newer K219 comparator.
- `fixed_role_seed_k.md`: fixed public roles for the seed scheme while
  retaining all logical membership-vacuity instances.
- `t_countermodel.md`: a full set-sized model for T and/or dual B when the
  original primitive positive equality is retained.
- `negative_atoms_restricted_l.md`: a limited core obstruction for the
  all-negative-atom proposal. This does not model the native K scheme.
- `ax_gate_counter_relaxation.md`: a sufficient whole-command interface
  allowing a residual parameter counter on selected gate inputs while
  preserving START and the complete proof-block reset construction.

The following scripts use only the Python standard library. Run them with
ordinary Python, without `-O`. Each writes its own JSON receipt next to
the script.

```sh
python check_membership_blind_detachment.py
python check_mp_conventions.py
python check_t_template.py
python check_negative_atoms_core_matrix.py
python check_shifted_even_codec.py
python check_boot_permutations.py
```

The bootstrap script optionally takes `--sites PATH` to bind its recorded
prefix effects to the first 37 entries of a literal source-sites JSON file.
Without that argument it checks the independently recorded prefix control
graph only. The packaged source-bound receipt records which file was used.
The separate encoding-side `audit_t_native.py` binds the countermodel's
formula templates to the literal Rocq definitions and theorem-rule list.

The finite tests are regressions or finite truth-table verifications of
explicit lemmas. None is represented as a new Rocq endpoint, an unbounded
source simulation theorem, or a certificate for a transition table.
The negative-equality dual-B bootstrap was additionally reviewed by the
independent encoding agent, who found no mathematical gap in its stated
scope; that review is not a formal replay.

The `_theory_qa.*` and rendered `theory_review-*.png` files are local layout
checks, not required deliverables. The exploratory `restricted_l_*` and
`prefix_codec*` files are not premises of any theorem in this packet and
need not be included in the final archive.
