# Replaying the mathematical audits

Run with Python 3 and its standard library. No third-party packages, network access,
proof search, or certificate generation are used.

From the extracted packet root:

```sh
python3 -B code/check_mathematics.py --out /path/to/fresh-output/mathematics_audit.json
```

The input root defaults to the parent of the script directory; `--root` can override
it. `--out` controls the only written output. If omitted, the output is
`evidence/mathematics_audit.json` under the input root. Use an external output path
when replaying a packet whose manifest must remain unchanged.

For an importing verifier, `audit(packet_root=None)` and its alias
`verify(packet_root=None)` return the deterministic result dictionary without
writing any file. The record has no timestamp or absolute host path. It includes
SHA-256 hashes of its exact inputs and of the checker itself.

## Exact checks

1. The ordered-commutation reader is implemented directly in this script. It
   imports neither the certificate generator nor its Hilbert helper. It checks
   all 600 stored nodes, each exact schema, topological parent references,
   modus ponens, hypothesis propagation, and theorem-only generalization. The
   two requested closed outputs have 488 dependency nodes, no hypotheses, and
   five closed GEN premises. The sole admitted commutation axiom has labels
   `(a,b)` and matrix `not(Box_b(Box_a(x)))`. Negative controls must reject an
   opposite-orientation axiom and generalization of an open hypothesis.
2. The scheduler recurrence is checked for 500,000 candidate summaries,
   including 1,000 explicitly expanded words and 997 complete Cantor diagonals.
   With tags MP=0, S=1, AX=c+2 and conservative weights 0, -1, +10, the exact
   conservative credit at cutoff one is one. Ten initial theorem heads leave
   a permanent nine-head margin by the separate all-natural induction in
   `proofs/permuted_credit.md`. The finite check corroborates that induction;
   it does not replace it. Both single-guard S and two-guard composite S-prime
   have this normal-return stack accounting.
3. The included independent fixed-certificate reader is loaded directly from
   `reference/transfer-parent/checks/check_fixed_certificate.py` to verify the
   inherited dominated-rho8 certificate. Its 3,728 proof nodes and 5,160 term
   nodes are checked, including exact I, K, Peirce, cd59, B, S, and unrestricted
   rho8 roots, explicit renamings, and domination witnesses. The generator and
   search procedures are not executed. Its native-zero normalization is only
   I(T,T)=T; a schematic integer leaf zero remains a metavariable.

The initial successful result is in `evidence/mathematics_audit.json`. A success
record is `MATHEMATICS_AUDIT_PASS`. This establishes the listed finite checks; it
does not independently certify the whole ZFC calibration, the ordinary credit
induction, the binary runtime, or blank startup. The inherited classical
interface used by ordered commutation includes retained rho6 for falsity and
double-negation elimination. No Lean/Rocq endpoint or 214-state table is claimed.

## LaTeX section

`report/ordered_commutation_section.tex` is include-ready and defines no global
macros or environments. It requires `amsmath` and `amssymb`. For standalone
compilation, wrap it in an ordinary LaTeX document with those two packages and
`\input{ordered_commutation_section.tex}` inside the document environment.
All of its cross-references use labels declared in that section. The main packet
report is the intended compiled document.
