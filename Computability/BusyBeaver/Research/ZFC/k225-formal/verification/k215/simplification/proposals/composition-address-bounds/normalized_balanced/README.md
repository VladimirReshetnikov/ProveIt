# Normalized K215 source proof with balanced lookup

This component composes two previously checked incoming refinements: the
1,426-row normalized source certificate and balanced binary-indexed lookup.
The exact all-register theorem and same-name public facade compile with closed
assumptions. The complete K215 binary/ZFC endpoint was not rebuilt here.

## New formal results

- `NormalizedBalanced.v`: generic equality of the new normalized tree checker
  with the incoming normalized list checker on the flattened valid tree;
  source halting equivalence follows from the inherited soundness proof.
- `NormalizedTree215.v`: exact 1,426-row tree, validity, exact flattening,
  height 12, and a uniform 12-node lookup bound.
- `Source215NormalizedBalanced.v`: exact `p215` versus `dagPerm` equivalence
  for every natural-valued register file.
- `LookupCost215.v`: actual `tsite`-classified counts of 32,961 tree visits,
  2,033,059 list visits, and 2,851 queries, all kernel-checked.
- `integration/`: the same public `K215F.Source215.p215_dagPerm` type and a
  separately compiled typed client.

The normalized certificate, pointer-padding soundness proof, path codec,
ordinary mirror lemma, and balanced lookup infrastructure are inherited from
`K215_Checked_Simplifications_2026-10-21` and
`K215_Certificate_Refinements_2026-10-21`. They are preserved rather than claimed
as new. The added generic composition file is 2,381 bytes. This number is not the
size of the complete soundness development.

## Reproduce

Coq 8.18.0 / OCaml 4.14.1, Python 3 standard library:

```
python3 reproduce.py --out /absolute/fresh/build --recursive
python3 lookup_metrics.py
python3 verify_metrics.py --build /absolute/fresh/build
```

The first command compiles every source prerequisite and the exact source
instance, facade, and client. `--recursive` also runs `coqchk` on the client and
its full dependency closure. The last command separately checks the exact
accounting lemmas; they do not enter source-equivalence soundness. Complete
recursive audits can take several minutes.

`verification/receipt.json` and logs record the actual proof checks. The first
concrete module attempt lacked an import; its failed log is retained separately.
Only the corrected source and successful subsequent proof enter the final
receipt. No axioms or admitted obligations were inserted. The Coq 8.18 aliases
are proved compatibility helpers; the original Rocq 9.1 input stays unchanged.

## Integration

The facade in `integration/Source215.v` replaces the production source theorem
with the same type. Put the helper modules on the load path or qualify them
uniformly under the desired project namespace, update `regenerate215.py` and
its data/build manifests, then rebuild `Correct215` and `CorrectDense215` under
the repository's Rocq 9.1 toolchain. Those final production gates remain open.
Do not replace only the generated facade while leaving its generator to emit
the old offset proof. The literal programs are byte-identical to the pinned
repository files; `upstream_binding.json` records that comparison.

The exact indexing counts concern constructor visits only. They do not measure
instruction-path decoding, segment arithmetic, proof elaboration, tree
construction, or total kernel time. No whole-build speedup is asserted.
