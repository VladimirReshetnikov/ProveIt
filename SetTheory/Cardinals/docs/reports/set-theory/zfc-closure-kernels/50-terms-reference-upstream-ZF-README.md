# ZF/ — verified Turing machines that halt iff ZF(C) proves a contradiction

**Smallest verified: 254 states, by Mira-Cult.** The 254-state machine
[`m254/machine/zfc_254.tm`](m254/machine/zfc_254.tm) is by Mira-Cult
([github.com/Mira-Cult/turing-machines](https://github.com/Mira-Cult/turing-machines)). [`m254/`](m254/) proves in Coq, with
no axioms, that it halts on a blank tape **if and only if ZFC is inconsistent**. The target ZF is the same
library formalization as below (CI job `zf-m254`):

```coq
Theorem zf254_halts_iff_ZF  : halts tm c0 <-> ZFc ⊢TC ⊥
Theorem zf254_halts_iff_ZFC : halts tm c0 <-> (ZFc + AC) ⊢TC ⊥
```

**Our own machines.** The 335-state, 2-symbol machine [`machines/R3Y1_335.tm`](machines/R3Y1_335.tm), started on a
blank tape, halts **if and only if ZFC is inconsistent**. This is proved end to end in Coq with no
axioms ([`stdzf_r3/`](stdzf_r3/), CI job `zf-stdzf-r3`):

```coq
Theorem zf335_halts_iff_ZF      : halts tm c0 <-> ZFc ⊢TC ⊥                (* ZF            *)
Theorem zf335_halts_iff_ZF_reg  : halts tm c0 <-> (ZFc + Reg) ⊢TC ⊥        (* ZF + Reg      *)
Theorem zf335_halts_iff_ZFC     : halts tm c0 <-> (ZFc + AC) ⊢TC ⊥         (* ZFC without Reg *)
Theorem zf335_halts_iff_ZFC_reg : halts tm c0 <-> (ZFc + Reg + AC) ⊢TC ⊥   (* ZFC           *)
```

- `halts`, `c0`: busycoq's TM semantics.
- `tm`: proved equal to the literal table of the `.tm` file.
- `⊢TC`: classical natural deduction of the Coq Library of Undecidability Proofs (Kirst & Hermes).
- `ZFc`: that library's ZF, with its separation and replacement instances universally closed.
- `Reg`: the regularity axiom.
- `AC`: Zermelo's choice-set axiom.

The relative consistency of regularity (well-founded sets) and of choice (Gödel's L) is formalized at
the level of derivations, in `stdzf_r3/regcon/` and `stdzf_r3/zfc/`, so that the ZF + Reg and ZFC statements
follow from the ZF one with no paper argument. (For an earlier mechanization of the relative consistency of
AC, inside Isabelle/ZF, see L. C. Paulson, "The Relative Consistency of the Axiom of Choice — Mechanized
Using Isabelle/ZF", LMS J. Comput. Math. 6 (2003).)

Coq proofs that five 2-symbol Turing machines, started on a blank tape, halt **if and only if** a
Hilbert-style formalization of ZF set theory (O'Rear's system `prov`) proves `v_0 e. v_0`:

```coq
Theorem zf_machine : halts tm c0 <-> prov (Wel v0 v0).
(* Print Assumptions zf_machine:  Closed under the global context *)
```

[`stdzf/`](stdzf/) then connects `prov` to the standard formalization of ZF in the Coq Library of
Undecidability Proofs (Kirst & Hermes). For the 354-, 336- and 335-state machines it proves end to end, in a
single build each (`stdzf/endtoend/354`, `stdzf_r3/endtoend/336`, `stdzf_r3/endtoend/335`):

```coq
Theorem zf354_halts_iff_ZF     : halts tm c0 <-> ZFc ⊢TC ⊥          (* ZF, schemas universally closed *)
Theorem zf354_halts_iff_ZF_reg : halts tm c0 <-> (ZFc + Reg) ⊢TC ⊥  (* ZF with regularity *)
(* plus the same for the library's function-symbol signature; all closed, no axioms *)
```

So the 335-, 336- and 354-state machines halt iff ZF is inconsistent, with or without regularity. No paper argument
remains; see [`stdzf/README.md`](stdzf/README.md).

| machine | states | origin | proof |
|---|---|---|---|
| [`machines/zf2.tm`](machines/zf2.tm) | 393 | Andrew Wade's machine, unchanged | [`verify/393/`](verify/393/) |
| [`machines/A361.tm`](machines/A361.tm) | 361 | Wade's framework; reworked program, same formal system | [`verify/361/`](verify/361/) |
| [`machines/B354.tm`](machines/B354.tm) | 354 | as A361, plus equivalent rewrites of EXT, REP and INF | [`verify/354/`](verify/354/) |
| [`machines/R3s336.tm`](machines/R3s336.tm) | 336 | bounded-fiber REP; POW and UNI dropped (derivable) | [`verify/336/`](verify/336/) |
| [`machines/R3Y1_335.tm`](machines/R3Y1_335.tm) | **335** | as R3s336, with B2 and B3 replaced by one scheme BY | [`verify/335/`](verify/335/) |

The 393/361/354 machines search the same formal system (`Logic.v` byte-identical in their proofs). The
336- and 335-state machines search a different but equiconsistent one (their own, shared `Logic.v`);
`stdzf_r3/` proves it equivalent to standard ZF.

## Background

The machine in this lineage has always been O'Rear's proof enumerator:
- the logic is Tarski's system S2 with O'Rear's modifications, plus the ZF axioms EXT, REP, POW, UNI
  and INF;
- wffs and proofs are encoded as Cantor-paired integers;
- the program builds every candidate proof and halts when it derives `v_0 e. v_0`.

Over the years it was compiled to successively smaller Turing machines:
- Yedidia and Aaronson, 7910 states (2016);
- Stefan O'Rear's NQL compiler, 1919 and then 748 states (2016);
- Johannes Riebel, 745 states (2023);
- Rohan Ridenour, 643 and then 636 states (2024);
- Andrew Wade, 588, 549 and 432 states (2025), with the 432-state machine listed on the bbchallenge wiki;
- Wade's current `turing_machine_explorer` repository
  (<https://codeberg.org/ajwade/turing_machine_explorer>, MIT No Attribution), which compiles the
  program to 393 states.

As far as we know, none of these machines had been formally verified before.

- **393:** `machines/zf2.tm` is Wade's `zf2.tm` unchanged. Rebuilding it from his `zf2.py` with the axiom
  order in his README reproduces it byte for byte.
- **361 (A361):** keeps Wade's framework and compiler and changes only the program:
  - the duplicated B6b and B8b clauses are removed;
  - each axiom clause's parameter roles are permuted, with the permutation found by search;
  - DET pops straight into a scratch register;
  - the B6a distinctness test consumes its inputs;
  - wff constructors tag by pairing directly;
  - push and select share one pair/unpair instance;
  - the equality test no longer uses a level-2 break;
  - the dispatch chain is capped at 7.
- **354 (B354):** A361 plus rewrites of the axiom text inside the program. EXT and REP have `/\`, `<->`
  and `=` commuted, and INF has its variables renamed. `verify/354/L1_B354.v` proves in pure
  first-order logic that each rewritten axiom and its original are interderivable. So the machine
  searches a system with exactly the same theorems, and the trusted `Logic.v` is unchanged.

- **336 (R3s336):** REP's functionality hypothesis `A. v1 ph -> v2 = v1` is replaced by a fiber BOUND,
  `A. v1 ph -> ( -. A. v0 ( v0 e. v2 -> v0 e. v1 ) -> v2 e. v1 )` (every image is a member or a subset
  of some set y). The scheme stays ZF-valid (each fiber lies in y u P(y)), and POW and UNI become its
  instances, so both clauses are dropped. EXT and INF are only flipped/renamed. `prov` changes, so this
  machine's link to ZF is the Coq development in `stdzf_r3/` (not a paper argument).
- **335 (R3Y1_335):** R3s336 with the propositional schemes B2 and B3 replaced by the single scheme
  BY = `p -> ( ( -. q -> ( ( q -> r ) -> -. p ) ) -> q )`. `verify/335/PropBasis.v` derives B2 and B3 from
  B1 + BY (and BY from B1-B3), so the machine targets the same `Logic.v` as 336. All eleven logical
  schemes of the original system were shown independent (countermodels), so none can simply be dropped.

[`generator/`](generator/) rebuilds `A361.tm`, `B354.tm`, `R3s336.tm` and `R3Y1_335.tm` byte for byte with `python mkcand.py A361.json A361`.
The generator is Wade's `TMBuilder.py`/`zf2.py` (unmodified) plus our program `zfp.py`.

## Checking

Build busycoq (<https://github.com/meithecatte/busycoq>, commit `bd2e36f`, Coq 8.20.1) far enough to have
`TM.vo`, then:

```
cd ZF/verify
BUSYCOQ=/path/to/busycoq/verify python3 check.py 335      # or 336, 354, 361, 393
```

`check.py` does three things:
1. It parses the `.tm` file independently and checks that the literal table `zf2_table` in
   `ZF2Dag.v` is exactly its transition table.
2. It compiles the proof.
3. It checks the statement of `zf_machine` and that `Print Assumptions` reports no axioms.

A full check takes about 5–12 minutes per machine. CI runs all five; see `.github/workflows/coq.yml`.

### What has to be trusted

- **busycoq's `TM.v`:** the definitions of `step`, `halts` and `c0`, the same ones used by the BB(5)
  proof and by `BB8/`–`BB10/` here.
- **The machine:** `ZFTM.v` defines `tm` and proves by computation (`tm_table`) that, for every state
  and symbol, `tm` gives exactly the transition listed in `zf2_table`. That includes the halting
  entries, so `zf2_table` has no extra or missing rows. `check.py` ties `zf2_table` to the `.tm` file.
- **The formal system:** `Logic.v`, about 100 lines. `prov` has the rules DET and GEN, the logical
  axioms B1–B4, B6a–B6c, B7 and B8a–B8c, and EXT, REP (a schema), POW, UNI and INF. Compare them with the
  header of O'Rear's [`zf2.nql`](https://github.com/sorear/metamath-turing-machines/blob/master/machines/2017-zf-sorear-748/zf2.nql).
  `E.` and `/\` are abbreviations.
- **Coq itself:** the Coq 8.20.1 kernel, including the `vm_compute` reduction machine. The table check,
  the boot run, the IP-space prefix and the DAG well-formedness checks are proofs by computation.

### The system versus standard ZF (formalized in `stdzf/`)

On its own, `zf_machine` is about `prov` exactly as defined in `Logic.v`. Earlier machines in this
lineage relied on two paper arguments to read it as "halts iff ZF is inconsistent": that `prov` is no
stronger than ZF, and that it is complete enough to reach ZF − Reg − AC (completeness of O'Rear's
Tarski-S2 variant, fixed-variable axioms, sharp REP). [`stdzf/`](stdzf/) replaces both with Coq
theorems:

- `prov (Wel v0 v0) <-> ZFc ⊢TC ⊥`, where `ZFc` is the minimal-signature ZF of the Coq Library of
  Undecidability Proofs with its separation/replacement instances universally closed. This is the
  library's own semantic axiom set. Its deductive theory leaves the instances open, and treats their
  parameters as constants.
- The same with regularity added (`ZFc + Reg`): the relative consistency of regularity, proved by
  relativizing derivations to the class of well-founded sets.
- The same for the library's function-symbol signature.
- One direction for the library's theories exactly as written: `minZFeq ⊢TC ⊥ -> prov (Wel v0 v0)`.

For the 354-state machine, `stdzf/endtoend/354/` compiles the machine proof and these theorems in one
namespace, so `halts tm c0 <-> ZFc ⊢TC ⊥` holds directly and `Logic.v` is only an internal
intermediate. The trust surface for that statement is described in `stdzf/README.md`. Only the
translation of "ZF is inconsistent" into this particular classical natural-deduction calculus remains
informal; all standard complete calculi agree on it.

### Proof structure (each `verify/N/`)

| layer | files | statement |
|---|---|---|
| TM ↔ register machine | `ZFTM.v`, `Sim*.v` | `halts tm c0 <-> rm_halts zf2 ([], regs0)` |
| path ↔ big-step semantics | `RM.v`, `RMEquiv.v` | `wf p -> rm_halts p ([], R) <-> iter_halts p R` |
| program ↔ abstract enumerator | `ZF2Dag.v`, `ProgLib.v`, `Prog.v` | one run of the root = one `enum_step` |
| enumerator ↔ provability | `Logic.v`, `Enum.v`, `L1*.v` | `enum_halts <-> prov (Wel v0 v0)` |
| assembly | `MainGlue.v`, `Main.v` | `zf_machine` |

Notes on the TM layer:
- The machine runs a boot of about 39,800 steps, then interprets Wade's register machine.
- Each dispatch cycle (select, inc, decnz on nonzero and on zero, break, continue, halt) is proved once,
  over symbolic register files.
- Wade's README warns that his framework never checks that the instruction pointer fits in front of
  the register file. Lemma `ip_space` proves that it always does: the first few hundred
  register-machine steps are computed, and after that, the decrements already executed guarantee
  enough space.

Notes on the logic layer:
- Soundness uses a decoder that is total on all numbers: every number decodes to some wff, and junk
  decodes to `v0 = v0`. This is needed because the machine really does push numbers that are not
  codes of any wff.
- Completeness compiles any derivation into the machine's proof encoding.

[`tools/`](tools/) has an independent Python simulator (`tmsim.py`), a DAG extractor and
register-machine simulator (`dag.py`), the TM-vs-register-machine cross-checker (`crosscheck.py`) and
the generator of `ZF2Dag.v` (`gen_coq_dag.py`).

## Credits

- **Stefan O'Rear:** the formal system, the encodings and the original NQL program.
- **Andrew Wade:** the `TMBuilder` framework and compiler and the 393-state machine. Every machine here
  is built with his compiler.
- **Rohan Ridenour, Johannes Riebel, CatsAreFluffy:** earlier improvements.
- **Maja Kądziołka:** busycoq.
