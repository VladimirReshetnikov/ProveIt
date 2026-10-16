# The R3 ZF machines (335 and 336 states) vs. the ZF of the Coq Library of Undecidability Proofs

Two machines search the "R3s" Hilbert system `prov` of `coq/Logic.v`: Tarski S2 logic plus EXT, a
**bounded-fiber replacement** scheme REP (O'Rear's fiber condition `z = y` replaced by
`z ⊆ y ∨ z ∈ y`), and INF; POW and UNI are derivable and are not axioms.

* `endtoend/machines/R3s336.tm` (336 states) uses `prov` itself.
* `endtoend/machines/R3Y1_335.tm` (335 states) uses `provY`: `prov` with the propositional schemes
  B2, B3 replaced by the single scheme BY = `a -> ((¬b -> ((b -> c) -> ¬a)) -> b)`;
  `provY_prov : provY a <-> prov a` (`endtoend/335/EquivY.v`, derivations in `PropBasis.v`) is part of
  that machine proof.

This package proves, in one Coq build per machine, that each machine halts iff the ZF of the Coq
Library of Undecidability Proofs (Kirst & Hermes, ITP 2021 / JAR 2023) is inconsistent. It has the
same shape as `../stdzf/` (the 354-state machine with O'Rear's original system); in the repository it
is `ZF/stdzf_r3/`. The standard-ZF side (`coq/`, `regcon/`) is shared by both machines.

## End to end (`endtoend/<n>/E2E<n>.v`, n = 335, 336)

    Theorem zf335_halts_iff_ZF         : halts tm c0 <-> ZFc ⊢TC ⊥
    Theorem zf335_halts_iff_ZF_reg     : halts tm c0 <-> ZFc_reg ⊢TC ⊥
    Theorem zf335_halts_iff_ZF_fun     : halts tm c0 <-> RegCon.Main.ZFc ⊢TC ⊥
    Theorem zf335_halts_iff_ZF_reg_fun : halts tm c0 <-> RegCon.Main.ZFcReg ⊢TC ⊥

and the same four `zf336_…` for the 336-state machine. For the 335-state machine also, via the
relative consistency of the axiom of choice (`zfc/`, below):

    Theorem zf335_halts_iff_ZFC        : halts tm c0 <-> (ZFc + AC) ⊢TC ⊥
    Theorem zf335_halts_iff_ZFC_reg    : halts tm c0 <-> (ZFc + Reg + AC) ⊢TC ⊥
Each machine proof (`endtoend/<n>/`, from `ZF/verify/<n>/` minus the files shared with `coq/`) is
compiled in ONE logical namespace with the standard-ZF development, so the intermediate `prov` is a
single constant and drops out of the trust surface. `halts`, `c0`: busycoq's `TM.v`
(`vendor/busycoq/`); `tm`: `endtoend/<n>/ZFTM.v`, proved equal inside Coq to the literal table
`zf2_table` of `ZF2Dag.v`, which `check.py` compares with the machine's `.tm` file.

## Statements via `prov` (`coq/Std_Main.v`, `regcon/MainR3s.v`, restated in `coq/Check.v`)

`T ⊢TC ⊥` is the library's classical theory derivability (`tprv`: natural deduction `FullND.prv`
with Peirce's law, from finitely many axioms of `T`).

| theorem | statement |
|---|---|
| `prov_iff_ZFc`                | `prov (Wel v0 v0) <-> ZFc ⊢TC ⊥` |
| `MainR3s.prov_iff_ZFc_reg`    | `prov (Wel v0 v0) <-> ZFc_reg ⊢TC ⊥` |
| `MainR3s.prov_iff_ZFc_fun`    | `prov (Wel v0 v0) <-> RegCon.Main.ZFc ⊢TC ⊥` |
| `MainR3s.prov_iff_ZFcReg_fun` | `prov (Wel v0 v0) <-> RegCon.Main.ZFcReg ⊢TC ⊥` |
| `minZFeq_to_prov`             | `minZFeq ⊢TC ⊥ -> prov (Wel v0 v0)` |
| `ZFeq_to_prov`                | `ZFeq ⊢TC ⊥ -> prov (Wel v0 v0)` |

All of them (6 + 4 end-to-end, 6 via `prov`, 5 in `zfc/Check.v`): `Print Assumptions` = "Closed under the global context".

## ZFC: the relative consistency of the axiom of choice (`zfc/`, restated in `zfc/Check.v`)

| theorem | statement |
|---|---|
| `ac_relcon`       | `(ZFc + Reg + AC) ⊢TC ⊥ -> (ZFc + Reg) ⊢TC ⊥` |
| `ac_reg_relcon`   | `(ZFc + Reg + AC) ⊢TC ⊥ -> ZFc ⊢TC ⊥` (with `regcon/Link.v`) |
| `zfc_relcon`      | `(ZFc + AC) ⊢TC ⊥ -> ZFc ⊢TC ⊥` |
| `ZFC_equicons`    | `(ZFc + AC) ⊢TC ⊥ <-> ZFc ⊢TC ⊥` |
| `ZFCReg_equicons` | `(ZFc + Reg + AC) ⊢TC ⊥ <-> ZFc ⊢TC ⊥` |

AC is `ax_ac` (`zfc/Z_wo.v`), one closed ∈/≡ formula, Zermelo's choice-set form:
∀x [(∀y∈x ∃z z∈y) → (∀y,y'∈x (¬ y≡y' → ¬∃z (z∈y ∧ z∈y'))) → ∃c ∀y∈x ∃z (z∈y ∧ z∈c ∧ ∀w (w∈y → w∈c → w≡z))].

These are object-level statements about derivability. The proof translates derivations: Gödel's L as
an inner model, with every derivation relativized to the class formula L by `regcon/Rel.v`. ZF+Reg
proves each axiom of ZF+Reg+AC relativized to L. Def(A) = Cl(A ∪ {A}) ∩ P(A) is the closure under 8
Delta_0 operations on finite assignments; a definability lemma (Coq recursion on the formula) puts
every A-definable subset of A into Def(A). Separation and replacement in L come from a reflection
principle for the L_α hierarchy. AC in L: ZF proves that every family in L_α has a choice set (canonical
well-orders built along the recursion); this is transferred to L, and (L_α)^L = L_α holds because
"Y = L_α" is a syntactically Sigma formula (checked by computation) with a unique solution in V. About
7,600 lines in 14 files (`Z_rel` … `Z_main`, see `zfc/Z_main.v`).

## The theories

* `ZFc` (`coq/Std_iface.v`, identical to `../stdzf/`): the library's `minZFeq` axioms (signature ∈, ≡;
  `FOL/Sets/minZF.v`: equality axioms, extensionality, empty set, pairing, union, power set, von
  Neumann infinity, separation and replacement schemes), with every scheme instance **universally
  closed**, the axiom set of the library's own semantic entailment. (The library's deductive
  `minZFeq`/`ZFeq` keep scheme parameters as fixed constants, so ∀-introduction can never generalize
  a parameter of a used instance; see `../stdzf/README.md`.) No regularity, no choice.
* `ZFc_reg` := `ZFc` + regularity `ax_reg'` (`regcon/MinZF.v`).
* `RegCon.Main.ZFc` / `ZFcReg` (`regcon/Main.v`): the same in the function-symbol signature.
* `minZFeq`, `ZFeq`: the library's theories verbatim; only "inconsistent -> `prov` proves `v0 ∈ v0`".

## Trust surface

For the end-to-end theorems: the machine's `.tm` file and the table check in `check.py`;
`ZFTM.v`'s use of `zf2_table`; busycoq's `TM.v`; `coq/Std_iface.v` (`ZFc`); `regcon/MinZF.v`
(`ax_reg'`) and `regcon/Main.v` (`ZFc`, `ZFcReg`); for the ZFC theorems `zfc/Z_wo.v` (`ACmat`, `ax_ac`); the library's definitions in
`vendor/undecidability/`; `endtoend/<n>/E2E<n>.v`; Coq 8.20. For the `prov` statements additionally
`coq/Logic.v` (byte-identical to `ZF/verify/{335,336}/Logic.v`) and `coq/Check.v`.

## Files

| path | content |
|---|---|
| `coq/Logic.v`, `L1_L*.v` | the R3s system `prov`; its pure-logic fragment |
| `coq/L1_R3s.v` | the machine's axiom texts are interderivable with `Logic.v`'s (pure logic) |
| `coq/Std_dB.v` … `Std_gen.v` | translations, ND soundness both ways, alpha-equivalence (as in `../stdzf/`) |
| `coq/Std_iface.v`, `Std_iface2.v` | target theories; set-theoretic obligations |
| `coq/Std_set*.v` | ND toolkit, generic closure theorem, Zermelo ↔ von Neumann infinity |
| `coq/Ax_rb.v`, `Ax_rbder.v` | bounded-fiber replacement in library syntax; library replacement, union, power set from it |
| `coq/Std_br*.v` | bridges between the R3s axioms and the library's |
| `coq/Std_glue.v`, `Std_ZFeq.v`, `Std_Main.v`, `Check.v` | assembly and statements via `prov` |
| `regcon/` | regularity and the signature bridge (zf-regcon); `MainR3s.v`: the R3s variants |
| `zfc/` | relative consistency of AC: relativization tools, ordinals, recursion, Def, L, reflection, axioms in L, well-orders, AC in L (zf-ac) |
| `endtoend/` | the machine proofs (335 incl. `PropBasis.v`, `EquivY.v`; 336), the machine files, `E2E<n>.v` |
| `vendor/` | unmodified library subset (MPL-2.0) and busycoq files (bd2e36f; MIT), with READMEs |

## Check

    python3 check.py        # uses $COQC, default `coqc` (Coq 8.20.x); prints CHECK PASS

It refuses `Admitted`/`admit`/`Axiom`/`Parameter` in `coq/`, `regcon/`, `zfc/`, `endtoend/` (vendored code is
covered by `Print Assumptions`), checks the literal tables, compiles everything from source in
dependency order, and requires every final theorem to be closed (6 in `coq/Check.v`, 5 in
`zfc/Check.v`, 6 in `E2E335.v`, 4 in `E2E336.v`).

## Credits

The Coq Library of Undecidability Proofs (Forster, Kirst, Hermes, Larchey-Wendling, et al.; ZF
formalization by D. Kirst and M. Hermes). Some proofs (`coq/Ax_rbder.v`) were written by Claude Haiku
5.5 subagents, and most of `zfc/` by Claude Opus 5.5 subagents; everything is machine-checked.
