# O'Rear's ZF proof system vs. the ZF of the Coq Library of Undecidability Proofs

The ZF Turing machines (393, 361, 354 states) halt iff O'Rear's Hilbert system
`prov` (`coq/Logic.v`) proves `v0 ∈ v0`. This development connects `prov` to the formalization of
ZF in the Coq Library of Undecidability Proofs (Kirst & Hermes, ITP 2021 / JAR 2023), so the machines
halt iff that ZF is inconsistent.

## End to end (`endtoend/354/E2E354.v`)

    Theorem zf354_halts_iff_ZF         : halts tm c0 <-> ZFc ⊢TC ⊥
    Theorem zf354_halts_iff_ZF_reg     : halts tm c0 <-> ZFc_reg ⊢TC ⊥
    Theorem zf354_halts_iff_ZF_fun     : halts tm c0 <-> RegCon.Main.ZFc ⊢TC ⊥
    Theorem zf354_halts_iff_ZF_reg_fun : halts tm c0 <-> RegCon.Main.ZFcReg ⊢TC ⊥

Only the 354-state machine (the smallest) is built end to end; the 361/393 proofs in `../verify/` compose the same way through the shared `Logic.v`. It is compiled in ONE logical namespace together with the machine
proof (`endtoend/<n>/`, copied from `ZF/verify/<n>/` minus the files shared with `coq/`), so the
intermediate `prov` is a single constant and drops out of the trust surface. `halts`, `c0`: busycoq's
`TM.v` (`vendor/busycoq/`); `tm`: `endtoend/<n>/ZFTM.v`, proved equal inside Coq to the literal table
`zf2_table` of `ZF2Dag.v`, which `check.py` compares with `endtoend/machines/<machine>.tm`.

## Statements via `prov` (`coq/Std_Main.v`, restated by type ascription in `coq/Check.v`)

`T ⊢TC ⊥` is the library's classical theory derivability (`tprv`: natural deduction `FullND.prv`
with Peirce's law, from finitely many axioms of `T`).

| theorem | statement |
|---|---|
| `prov_iff_ZFc`        | `prov (Wel v0 v0) <-> ZFc ⊢TC ⊥` |
| `prov_iff_ZFc_reg`    | `prov (Wel v0 v0) <-> ZFc_reg ⊢TC ⊥` |
| `prov_iff_ZFc_fun`    | `prov (Wel v0 v0) <-> RegCon.Main.ZFc ⊢TC ⊥` |
| `prov_iff_ZFcReg_fun` | `prov (Wel v0 v0) <-> RegCon.Main.ZFcReg ⊢TC ⊥` |
| `minZFeq_to_prov`     | `minZFeq ⊢TC ⊥ -> prov (Wel v0 v0)` |
| `ZFeq_to_prov`        | `ZFeq ⊢TC ⊥ -> prov (Wel v0 v0)` |

All six: `Print Assumptions` = "Closed under the global context".

## The theories

* `ZFc` (`coq/Std_iface.v`): the library's `minZFeq` axioms (signature ∈, ≡; `FOL/Sets/minZF.v`:
  equality axioms, extensionality, empty set, pairing, union, power set, von Neumann infinity, and
  the separation and replacement schemes), with every scheme instance **universally closed**.
  This is exactly the axiom set of the library's own semantic entailment, which demands the axioms
  under every assignment. Why closed: the library's deductive `minZFeq`/`ZFeq` keep the free
  variables of scheme instances as fixed parameters, and ∀-introduction requires a shifted context,
  so a derivation can never use a separation/replacement instance whose parameter is a locally
  generalized variable (ordinary ZF reasoning needs this; O'Rear's GEN applies to axiom instances).
  Neither regularity nor choice is included (the library's ZF has neither; nor does `prov`).
* `ZFc_reg` := `ZFc` + regularity `ax_reg'` (`regcon/MinZF.v`).
* `RegCon.Main.ZFc` / `ZFcReg` (`regcon/Main.v`): the same theories in the library's function-symbol
  signature (`FOL/Sets/ZF.v`: Skolem symbols for ∅, pairing, ⋃, power set, ω).
* `minZFeq`, `ZFeq`: the library's theories verbatim (open scheme instances). Only the direction
  "inconsistent -> `prov` proves `v0 ∈ v0`" is proved; the converse is a parameter-elimination
  question not addressed here.

## Trust surface

For the end-to-end theorems: the machine files `endtoend/machines/*.tm` and the table check in
`check.py`; `ZFTM.v`'s use of `zf2_table`; busycoq's `TM.v`; and the items below except `Logic.v`.
For the `prov` statements additionally `coq/Logic.v` (byte-identical to `ZF/verify/{393,361,354}/Logic.v`).

* `coq/Std_iface.v`: the definition of `ZFc` (`ZF0`, `ZF0base`, `closedf`);
* `regcon/MinZF.v`: `ax_reg'`; `regcon/Main.v`: `ZFc`, `ZFcReg` (function-symbol signature);
* the library's definitions in `vendor/undecidability/` (syntax, `FullND.prv`, `tprv`, `minZF.v`, `ZF.v`);
* `coq/Check.v`, `endtoend/<n>/E2E<n>.v` (the restated statements) and Coq 8.20.

## Files

| path | content |
|---|---|
| `coq/L1_L*.v` | pure-logic fragment of `prov`: deduction theorem, Leibniz, specialization, alpha |
| `coq/Std_dB.v`, `Std_F.v` | named → de Bruijn; every `prov` axiom and rule is valid in library ND |
| `coq/Std_tr.v`, `Std_H.v` | de Bruijn → named; library classical ND is sound for `prov` |
| `coq/Std_alpha.v`, `Std_gen.v` | alpha-equivalence theorem; closures; round trip |
| `coq/Std_iface.v`, `Std_iface2.v` | target theories; set-theoretic obligations |
| `coq/Std_set*.v` | ND toolkit, generic closure (recursion) theorem, Zermelo ↔ von Neumann infinity |
| `coq/Std_br*.v` | bridges between O'Rear's axioms and the library's |
| `coq/Std_glue.v`, `Std_ZFeq.v`, `Std_Main.v`, `Check.v` | assembly and final statements |
| `coq/Haiku_pow.v` | experiment record (not compiled by `check.py`; its proof is in `Std_brpow.v`) |
| `regcon/` | relative consistency of regularity and the signature bridge (zf-regcon) |
| `endtoend/` | machine proofs (from `ZF/verify/`), machine files, end-to-end theorems |
| `vendor/undecidability/` | unmodified library subset (MPL-2.0), see its README |
| `vendor/busycoq/` | unmodified busycoq `TM.v`, `Helper.v`, `LibTactics.v` (bd2e36f; MIT) |

## Check

    python3 check.py        # uses $COQC, default `coqc` (Coq 8.20.x); prints CHECK PASS

It refuses `Admitted`/`admit`/`Axiom`/`Parameter` in our sources (`coq/`, `regcon/`, `endtoend/`;
vendored code, e.g. busycoq's module-type `Parameter`s, is covered by `Print Assumptions`), checks the
three literal tables, compiles everything from source in dependency order, and requires every final
theorem to be closed (6 in `Check.v`, 4 per machine).

## Credits

The Coq Library of Undecidability Proofs (Forster, Kirst, Hermes, Larchey-Wendling, et al.; ZF
formalization by D. Kirst and M. Hermes). The proof of `bridge_POW` (`coq/Std_brpow.v`) was written by
a Claude Haiku 5.5 subagent (experiment record `coq/Haiku_pow.v`); everything is machine-checked.
