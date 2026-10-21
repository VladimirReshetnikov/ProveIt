# Z215: zero-valued spare blocks and a two-truth startup

**Result:** a materially different **215-working-state, two-symbol** blank-tape consistency machine. The ordinary mathematical proof, formalizable in ZFC and explicitly using the accepted numerical-calculus calibration, gives

> ZFC proves: nonhalting of Z215 on blank tape if and only if Con(ZFC).

This packet does **not** claim a 214-state machine, an unconditional nonhalting theorem, a minimum-state theorem, or a new exact-table Lean/Rocq endpoint.

Read [report.pdf](report.pdf) or its source [report.tex](report.tex). The PDF includes the complete dense transition table. The new proofs and the inherited assumptions are stated separately.

## Exact construction

The parent is the primary `candidate-k215` at ProveIt commit `32498004963846db7655eedce7e94f8c88f6fa8a`. Make only these changes:

| Item | Parent | Z215 |
|---|---|---|
| Initial native state | 0 | 74 |
| Native row 198, read 0 | write 1, L, next 40 | write 0, L, next 40 |

All other rows and the complete register source remain byte-equivalent after canonical serialization. The native table has 215 working labels, 430 rows, dispatcher 84, and halt 254. The dense table has working states 0–214, initial 0, dispatcher 83, and halt 215; the halt is not counted. Tape is two-way infinite and initially all zero, with head at position 0. There is no external setup.

- [Native machine](machine/z215.native.tm), SHA-256 `423c755b04ed0cd5be199178686657bf721540b858d0fb8f491239622d6d99fa`.
- [Dense machine](machine/z215.tm), SHA-256 `d7a9d557cd08ddb0ebb1960b7fed4892db64bd38af5e0c4ae3bff9a594838825`.
- [Exact source](machine/sites215.json), SHA-256 `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`.
- [Exact state bijection](machine/canonicalization.json).

Every source increment appends `B(0)=01` instead of `B(1)=011`, where `B(v)=0 1^(v+1)`. Thus after the same k increments from otherwise matched frames the appended spare region has 2k cells instead of 3k, saving k cells and k one-symbols. This concerns that spare region, not total space or elapsed-time complexity. All 215 working states are reachable in the finite transition graph. The number of one-writing rows changes from 189 to 188, ruling out state-renaming equivalence to the parent, including after tape reflection.

## Complete verification and the new proof idea

The unchanged symbolic checker, with its existing append parameter set to 0, proves **all 6,176** guarded cases for the 4,751 source primitives. The derivations use 1,698,790 symbolic rule applications, cover all 430 rows including the rederived block schemas, and have minimum affine duration constant 6. The domain is every natural primary register tuple and gap, an arbitrary nonempty finite list of natural spare values, and the entire zero exterior. Unary and list induction make this an unbounded claim.

Blank execution reaches native dispatcher 84 in **117,004 transitions**, with head −4, header 80, gap 20, logical registers

```
[N,T,W,A,D,H,X,Y,L] = [1,0,5,0,0,0,0,0,0]
```

and 67 spares, all zero except the third and eighth, which are one. The full terminal tape has 86 one-cells, from −5 to 240. An independent reader replays every transition in both presentations and reconstructs the entire terminal frame.

The stack is `5=P(0,P(0,1))`: two truth codes above a potentially unsafe tail. The new all-natural theorem proves that the exact command-local enumeration NIP0/DROP1/MP2/AX≥3, starting with candidate 1, has conservative stack debt at most 2. Its proof uses 666 explicit base candidates, two Cantor prefix-sum transforms, and diagonal induction. Consequently an arbitrary tail below two truth entries is never read. The strong compiler works over arbitrary retained tails, supplying completeness. This is not the older common-field-reader protected-tail theorem.

## Reproduction

Run from this directory with Python 3.10 or later. Only the standard library is needed.

```sh
python3 -B verify.py
```

This verifies all manifest-bound bytes, independently reconstructs the table and dense presentation, replays the complete native/dense startup, audits every saved runtime case, recomputes the scheduling premises, checks the literal source field arities and test-before-pop order, checks the 22-node logical certificate, and runs the secondary packet's portable verification. It does **not** rerun every symbolic derivation.

For complete fresh symbolic derivations, use a nonexistent output directory:

```sh
python3 -B replay_runtime.py --out /tmp/z215-runtime
```

The replay compares every deterministic machine, case, startup, and review artifact with the delivered files; only elapsed time is excluded. The original complete symbolic run took about 133 seconds. The retained checker is an ordinary mathematical verifier, not a proof-assistant kernel.

For exact reconstruction alone:

```sh
python3 -B reconstruct.py --out /tmp/z215-reconstructed
```

To rebuild the paper with standard TeX Live:

```sh
python3 -B code/make_machine_table.py
pdflatex report.tex
pdflatex report.tex
```

The finite schedule proof files are under [proof/](proof/). The complete runtime case list and blank trace are deterministic gzip JSON under [verification/](verification/). The included parent subset makes reconstruction and runtime replay independent of the current repository checkout.

## Additional results

### A second substantive 215-state machine

[research/command_family/](research/command_family/) contains `partialcb120`, combining the previously proposed shared-CB1 refill scheduler with DROP/NIP/MP command order. It has a fresh full 6,177-case runtime proof and an 88,746-step exact blank prefix. Its ordinary consistency proof is included. Native SHA-256:

`4f21c5836598482195191cf3a4f5926062cd14259c25713979e663848b09c584`.

The same packet records all six command-order allocations and their separate status. Order 021 actually halts and is rejected; 012, 102, 201 remain research-only. No source grammar count or incomplete startup scan is presented as a calibrated machine.

### A partial formalism result

[research/alias_free/](research/alias_free/) gives a 22-node, explicit-substitution proof deriving identity, weakening, and Peirce's law from only two subterm-bounded dominated-rho8 schema families. It uses no truth constant or implication alias. It applies to every operation `I_j(a,b)=4P(a,b)+j`, j ≥ 0. It does **not** prove distribution S, composition B, unrestricted rho8, or full consistency calibration of a new encoding. Z215's proof does not depend on this partial result.

## Dependencies and attribution

The principal new contributions are the zero-spare table/startup, fresh runtime verification, current-schedule debt-two theorem, source-focused review, secondary composition, and scoped alias-free derivation. The numerical calculus, strong compiler, binary architecture, runtime induction checker, and older refill idea retain their original provenance. See [NOTICE.md](NOTICE.md), [baseline/](baseline/), and [licenses/](licenses/). Inherited documents retain their historical relative repository references; the new entry points above are portable within this archive.

The complete historical ZFC/numerical-calculus calibration is an explicit imported theorem from the pinned ProveIt snapshot. This packet includes the immediate source/compiler proof but is not a replacement for the entire repository's proof ancestry. Separate reviews here are independent work inside this research collaboration, not an external human endorsement.
