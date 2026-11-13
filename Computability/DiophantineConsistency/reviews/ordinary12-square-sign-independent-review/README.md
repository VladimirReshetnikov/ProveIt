# Independent review of the square-only sign search

The reviewed sign-search source has SHA-256
`4472d0c6f9a7a6402e180978c3bf1d62e74e143177d078ea6ddd3d9d18806377`
and its recorded output SHA-256 is
`f8652ff1e46813ff4c24fc372c037f390a6a9e3cbbb54c7726679afeb59c701e`.
It first pins and executes the neighboring node-value search at source hash
`98f54938a6eb1a158ffca98581dd5836300e13a6d07f9340ca52ab8ae55f3949`;
that source checks the graph and restored coefficient payloads. The complete
sign-search output reproduced byte-for-byte in this review. Source, base,
graph, binding and all four gzip inputs were unchanged at the postcheck.

An independently implemented operand-position scan confirms that the only
eligible graph nodes are `Dstar`, `Z`, `f`, `polarA`, and `vn`: each has at
least one consumer and every direct consumer multiplies it by itself. A
sign flip changes no such consumer because `(-x)*(-x)=x*x`, so later rows
remain unchanged by induction. Independent integer evaluations checked all
five flips at seven assignments. A synthetic node with both a square and an
unsquared consumer was excluded by both the author search and the independent
scan; changing its sign demonstrably changes that synthetic output.

[`audit.py`](audit.py) independently enumerates the **full implemented
class** for both port modes, directly evaluating every second-gate operation
and square rather than using the author's inverse and square-root pruning.
In each mode it evaluated 72,767 first gates, 26,043,028 second-gate
operations and 72,767 squares. The resulting eligible sets, original live
counts and candidate sets match the recorded empty results. The verified
prime is `1000000007`, and neither recorded pass has a zero target or
nonconstant operand sample; multiplication by literal zero therefore cannot
match a sampled target. As in the base search, `t+t` is covered in value and
live count by `t*2`, and `t-t` cannot match these nonzero targets.

The independently constructed positive control has 96 live gates. It
reproduces all five recorded modular candidates, including the exact
95-live-gate replacement `Z := folded_q3Bt - g34`: this negates the
original controlled `Z`, whose only consumers square it. A separate small
synthetic control exercises an actual second-gate `t*t` reduction and
matches the author's candidate set. The full enumeration is an external
check at the specified samples; modular survivors would still require exact
proofs.

The independent author-side wrapper exited 0. Source SHA-256:
`eda47d0d076ae1f1491a223bddb47951071f8fe458fbf86c9cbee5f816642193`;
wrapper SHA-256:
`9aefd8c411f9c132662ea3fd8d9610ac55a412fe7b064774c051c6c1467bfc1e`;
result SHA-256:
`cdea29c6037070231ed01064e6c56aab72ed7d623e51880bd1de196a252dad08`;
terminal receipt SHA-256:
`43b5b94dad545207c57e62799cb6ef077b236d2f44cd9fdec10cf7930f4ded2b`.
The actual command and outputs are retained in
[`terminal-attempt02`](terminal-attempt02/) and
[`observations-attempt02`](observations-attempt02/); an earlier successful
run before the additional synthetic controls is retained as attempt 01.
To repeat, run `python3 -I -B audit.py /tmp/square-sign-audit-NEW` with a
fresh output directory; elapsed time is recorded and varies by run.

This review establishes no Lean theorem or global optimum. It does not cover
arbitrary non-square downstream contexts, several simultaneous rewrites,
longer expressions, different encodings, file/PDF interpretation, or an
iPRA derivation. The fixed-port payload decoding remains external, and all
file guards are point-in-time.
