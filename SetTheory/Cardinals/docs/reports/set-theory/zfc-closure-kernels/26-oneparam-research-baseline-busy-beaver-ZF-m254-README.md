# A verified 254-state Turing machine that halts iff ZFC is inconsistent

**The machine is not ours.** [`machine/zfc_254.tm`](machine/zfc_254.tm) was designed and built by
**Mira-Cult** ([github.com/Mira-Cult/turing-machines](https://github.com/Mira-Cult/turing-machines)).
It is the final table of their audited "ZFC254" reduction (2026-09-30), copied byte for byte:

```
sha256 d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb  machine/zfc_254.tm
```

The author's own work includes the source program, the set theory and compact proof calculus it searches,
the new single-marker interpreter, the state merges, and a written argument with extensive executable
audits. What this directory adds is a **Coq proof, with no axioms, of the end-to-end statement**:

```coq
(* coq/e2e/E2E254.v *)
Theorem zf254_halts_iff_ZF  : halts tm c0 <-> ZFc ⊢TC ⊥.          (* ZF  *)
Theorem zf254_halts_iff_ZFC : halts tm c0 <-> (ZFc + AC) ⊢TC ⊥.   (* ZFC *)
Theorem zf254_halts_iff_SIR : halts tm c0 <-> SIR ⊢TC ⊥.          (* the theory the machine searches *)
(* Print Assumptions: Closed under the global context (all three) *)
```

- `halts`, `c0`: busycoq's TM semantics (blank tape, start state 0).
- `tm`: built from the literal table `Table254.v`. [`check.py`](check.py) checks that this table is exactly
  `machine/zfc_254.tm`.
- `⊢TC`: classical natural deduction of the Coq Library of Undecidability Proofs (Kirst & Hermes).
- `ZFc`: that library's ZF, with separation and replacement instances universally closed. This is the
  same target as our 335-state theorem in [`../stdzf_r3/`](../stdzf_r3/).
- `AC`: Zermelo's choice-set axiom (via the relative consistency of AC in [`../stdzf_r3/zfc/`](../stdzf_r3/zfc/)).
- `SIR`: the author's nonextensional set theory, C_P + global-image collection + irreflexivity, in the
  library's syntax.

## Checking it

```
cd ZF/m254
python3 check.py          # coqc from $COQC, default `coqc` (Coq 8.20.x)
```

It refuses `Admitted`/`admit`/`Axiom`/`Parameter` in our sources, checks the table's hash and that
`Table254.v` equals the `.tm` file, compiles the whole dependency closure of `E2E254.v` from source,
and requires all three `Print Assumptions` to report `Closed under the global context`. It uses the
vendored library, busycoq, `ZF` (`../stdzf/coq`), `RegCon` and `ZFC` (`../stdzf_r3/`). CI job: `zf-m254`.

## Proof structure

| Layer | Directory | Statement |
|---|---|---|
| TM ↔ register machine | [`coq/tm/`](coq/tm/) | `tm254_rm : halts tm c0 <-> rm_halts p254 ([], R0)` |
| register machine ↔ enumerator | [`coq/prog/`](coq/prog/) | `prog254 : rm_halts p254 ([], R0) <-> enum254_halts` |
| enumerator ↔ the machine's calculus | [`coq/logic/`](coq/logic/) | `L1_254 : enum254_halts <-> thm254 1` |
| calculus ↔ natural deduction over SIR | [`coq/logic/`](coq/logic/) | `bridge254 : thm254 1 <-> SIR ⊢TC ⊥` |
| SIR ↔ ZF | [`coq/settheory/`](coq/settheory/) | `S_equicons : SIR ⊢TC ⊥ <-> ZFc ⊢TC ⊥` |

- **TM layer.** It does not use the author's 261-state named table or the merge certificates. A
  Coq-verified symbolic executor runs the final 254-state table directly, at every one of its 6,460
  instruction sites, over tapes with symbolic run lengths. Four register-file lemmas cover arbitrary
  register values and the growing tail of spare zero blocks. The 264,982-step blank-tape boot is checked by
  computation. It ends with `nextproof = 2`, which is why the start state is `R0 = upd regs0 0 2`.
- **Program layer.** The decoder tree `p254` (from the author's `paths.json`) is related by a checked
  3,010-entry path-bisimulation certificate to the 219-node program that Wade's TMBuilder compiles from
  the author's `source.py`. That program is then shown to run one step of the abstract enumerator per
  loop, symbolically, without evaluating any formula code.
- **Logic layer.** The formula coding is `4·P(x,y)+tag` with the dual Cantor pair, and code 1 = `v0 ∈ v0`
  plays the role of falsity. Soundness: every stack entry is a theorem of the code-level calculus.
  Completeness: every derivation compiles into a proof program from arbitrary leftover data. The bridge
  decodes the eight logical rows (one is Łukasiewicz's single implicational axiom; K, S, B and Peirce are
  derived from it in `CD254.v`) and the gated container/collection bundle, both ways.
- **Set-theory layer.**
  - (ZF → SIR) The author's bisimulation-quotient interpretation of ZF in the nonextensional theory, with
    extensionality of the quotient as the hardest lemma.
  - (SIR → ZF) SIR is relativized to Gödel's L inside ZF + Reg, and Reg is then removed with
    `../stdzf_r3/regcon`.

Design notes for each layer are in [`design/`](design/). Generators and validation scripts are in
[`tools/`](tools/). They read the author's bundle files (`paths.json`, `source.py`), which are not
redistributed here; `check.py` does not need them.

## Notes on the author's argument

We found no error that affects the result. Points that differ from, or simplify, the author's write-up:

- The irreflexivity axiom IR is essential to soundness. It is what makes the alias code 1 = `Rel(0,0)` = F
  sound. It also covers the `a = b` collisions, which the machine's freshness gate allows. The gate
  `c ≠ a, b` is essential, too: with `c = b` the container clause would assert a self-membership.
- The bisimulation relation can be defined with fewer witnesses than in the write-up.
- The ZFC-proves-SIR direction is formalized through L rather than through V_α.

The halting set of the table had not been checked end to end before. It now is, in Coq, under the trust
surface above: busycoq's `TM.v`, the library's ND system and ZF axioms, and the Coq kernel.
