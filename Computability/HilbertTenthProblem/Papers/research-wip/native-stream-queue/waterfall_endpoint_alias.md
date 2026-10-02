# Canonical endpoints do not certify the 46-clock Waterfall history

The fixed Iijil 46-clock matrix admits a nonnegative, nonhalting count vector `v` with

    Mv = 194·1,     sum(v)=62,     control_count(v)=10.

Adding it to the supplied seven-macrostep halting example preserves every deadline difference, its complete canonical halt endpoint, and the report's potential/time equation. It falsely changes the exact first-halt data from `(C,k,tau)=(189,7,428)` to `(251,17,622)`.

This is a counterexample to the explicit endpoint-only necessary-condition bundle below. It is **not a defect in the supplied report's bounded quadratic certificate or macrostep theorem**: those retain ordered transitions and every-prefix guards. It rules out replacing that machinery by this particular bundle on the actual universal matrix, rather than only on the report's separate three-clock example. It does not rule out nonlinear, order-sensitive, or other topology/history-aware Diophantine certificates.

## Frozen sources and replay

Archive `docs/incoming/Waterfall_Diophantine_Certificates.zip` has SHA-256
`b5d3ee90f9631695afc3c6f34f765b617eb9c631c65ab32705cf3d0e8811a9fc`.
The checker pins these archive members:

| Member under `waterfall-diophantine/` | SHA-256 |
|---|---|
| `source/UniversalTM15x2.twm.txt` | `52cfed3f6cba671ed7b166c126288d555ed687b74622ae5a9aaa5bee1345e46a` |
| `source/UniversalTM15x2.tm.txt` | `ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae` |
| `replay/verify_frontend.py` | `951c3482067c6754f23f3ad4cf21e13efe32f51ec9eed599bce02cac6117589d` |
| `paper/waterfall-diophantine.tex` | `22d6fc7aa755dcd3f6043f1b7472a82f6df2221bc3b21582a9c0fa76372a4e2f` |

The original creator's [matrix](https://github.com/Iijil1/MTGPrograms/blob/main/Examples/UniversalTM15x2.twm.txt) is the primary machine source. The included matrix's 47-by-47 serialization has one metadata coordinate. Source rows are trigger vectors; `M` here uses source columns, so `Mv` is computed by summing serialized trigger rows with coefficients `v_i`.

The arithmetic checker reads source bytes directly and imports no delivered Python module. It safely extracts the pinned archive to a temporary directory, or accepts a caller-supplied extracted root after checking all four member hashes. Every mathematical check uses explicit exception-producing checks, including under `python -O`; no CAS, optimizer, floating-point operation or search is used in replay. The witness was originally found by rational linear programming and is now verified solely by its 46 literal integer identities.

```sh
python waterfall_endpoint_alias.py --archive /path/to/Waterfall_Diophantine_Certificates.zip --expect waterfall_endpoint_alias.json
```

API: `verify(*, archive=None, source_root=None)` requires exactly one argument. `source_root` names the `waterfall-diophantine` directory. Archive-mode receipts include the checked archive hash; root-mode receipts attest only the checked members and intentionally omit the archive hash. `--output FILE` writes a deterministic receipt; the default prints it. No retained source or report receipt is modified.

The author writer and a separate fresh `--expect` replay passed. Python SHA-256 is `0fae44cec255d3387747a24cd9b97df3c22e090c8a3299ccc6d7f6a0b098090b`; saved JSON SHA-256 is `0dc80f4fef4e9eafa840f3fb3b07cdbe0451b7e6f7d75b3159b364fbe1cf71ff`.

## The exact rejected condition bundle

Let `h=TransJ1`, and let `a=can(A,0,6,0)` be the same fixed initial deadlines as the report's worked example. The bundle supplies natural counts `p_i`, natural terminal tape halves `Lf,Rf`, and natural `C,k,tau`, and requires:

1. `p_h=0`, `C=sum_i p_i`, and `k=sum_{q,s} p_Trans(q,s)`.
2. `a+Mp=can(J,1,Lf,Rf)+(tau-1)·1` in all 46 coordinates.
3. The endpoint has its strict unique minimum at `h`, with value `tau`.
4. `tau=1+2C+7k`.

Every genuine first-halt prefix satisfies these conditions. Requiring the article's additional fixed linear potential identity adds no protection: it follows from its source-column identities and is checked independently here. Likewise, any linear combination of the complete endpoint equations already belongs to this bundle.

The bundle does **not** include arbitrary previous-self-reset inequalities, word-order constraints, a guessed legal permutation of the counts, or the source's five residuals and two complementarity terms per macrostep. No counterexample to those stronger systems is asserted.

## Actual first halt, computed independently

Starting from `a`, repeatedly find the unique minimum of the current 46 deadlines, record its clock and timestamp, and add that source trigger row. Halt before updating `TransJ1`. The checker does this directly, without the macrostep frontend or the grouped quadratic compiler.

All 189 nonhalting selections are strict and timestamps increase. The next unique minimum is `TransJ1` at time 428. There are seven control-clock firings. The final vector is exactly

    can(J,1,0,11) + 427·1.

Thus the actual final halves are `Lf=0,Rf=11`. The receipt retains the full 189-event clock/timestamp trace, all 46 initial/final deadlines and all 46 base counts `p*`. The nonzero base counts are:

| Clock | Count | Clock | Count |
|---|---:|---|---:|
| LeftTape | 7 | RightTape | 7 |
| LeftTemp | 7 | RightTemp | 7 |
| LeftTrans | 58 | RightTrans | 16 |
| LeftDiv0 | 25 | LeftDiv1 | 22 |
| LeftMult | 18 | RightMult | 8 |
| LeftWrite0 | 1 | LeftWrite1 | 1 |
| RightWrite0 | 2 | RightWrite1 | 3 |
| TransA0 | 1 | TransB0 | 1 |
| TransC0 | 1 | TransG0 | 1 |
| TransG1 | 1 | TransH0 | 1 |
| TransI1 | 1 | | |

Unlisted counts, including the halt count, are zero. Summing gives `C*=189` and `k*=7`; `1+2·189+7·7=428`.

## Fixed extra count witness and false endpoint

All unlisted entries of the following `v` are zero:

| Clock | Count | Clock | Count |
|---|---:|---|---:|
| LeftTape | 10 | RightTape | 10 |
| LeftTemp | 10 | RightTemp | 10 |
| LeftDiv0 | 1 | RightDiv0 | 1 |
| LeftWrite0 | 6 | LeftWrite1 | 1 |
| RightWrite0 | 2 | RightWrite1 | 1 |
| TransA0 | 1 | TransB0 | 1 |
| TransC0 | 1 | TransG0 | 1 |
| TransH0 | 1 | TransI0 | 1 |
| TransN1 | 2 | TransO0 | 2 |

These are nonnegative integer counts, with halt entry zero, total 62 and ten control firings. Literal multiplication with the pinned matrix gives `Mv=194·1`. In particular `194=2·62+7·10`, as the independently checked potential also requires.

Set `p=p*+v`, keeping the initial input unchanged. Then

    a+Mp = can(J,1,0,11)+621·1,
    C=251, k=17, tau=622=1+2·251+7·17.

All 45 other endpoint deadlines are strictly greater than 622, since the canonical halt vector has unique minimum 1. Hence every listed endpoint condition passes. But determinism and the strict independent event replay prove that the run from this very same `a` has already halted at 428 after 189 firings. There is no legal first-halt history with the supplied 251 nonhalting counts. No choice of ordering can repair this: every legal prefix from `a` is forced until that earlier halt.

More generally `p*+n v` passes the bundle with

    C=189+62n, k=7+10n, tau=428+194n

for every natural `n`, and is false for every `n>=1`. This infinite alias family follows from the checked integer identity; it is not an extrapolation of a finite sample.

## Consequence for unbounded compression

Deadline differences and linear flow/timing invariants are useful bookkeeping, but this fixed witness proves they do not recover event order even when both endpoints are complete canonical machine configurations. Any proposed fixed-dimensional replacement needs an additional mechanism that rejects this family.

A broader, separately scoped obstruction is immediate: a finite existential formula using only fixed integer affine equalities, inequalities, congruences and finite Boolean combinations defines a Presburger set and has a decidable membership problem. It therefore cannot characterize the full c.e.-complete halting set on raw `(L,R)` for this universal matrix. Nonlinear Diophantine witnesses, digitwise history selection, or a genuinely different input interface lie outside that obstruction. The report already retains the necessary unbounded-history distinction, and neither result gives a new universal arithmetic-operation bound.
