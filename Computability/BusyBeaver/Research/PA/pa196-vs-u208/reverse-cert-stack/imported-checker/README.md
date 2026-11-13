# Existing PA196 checker constructors for command extraction

The imported development already supplies the concrete checker and
certificate constructors assumed abstractly in the adjacent
[command-extraction note](../COMMAND-EXTRACTION.md). This inventory gives their
exact parameter order and identifies what still has to be joined together.
It is not a proof of the desired PA-internal consistency equivalence.

The exact checker returns `a+1` for an accepted proof of numeric formula `a`,
and zero for rejection. Its
[`verifyValue` and `verifyGraph`](../../../jamesyc-upstream/pa196/PA196/Arithmetic/Checker.lean)
are connected by `Checker.verify_graph`; `Checker.verify_total_unique`
proves totality and uniqueness in every model of IΣ₁, and
`Checker.pa_proves_verify_total` states totality in PA. The input code is
`pair(fuel,tree)`. Each tree is `pair(tag,payload)` and payload arguments
are right-nested Cantor pairs ending in zero:

```
pack2(a,b)   = pair(a,pair(b,0))
pack3(a,b,c) = pair(a,pack2(b,c))
pack4(a,b,c,u) = pair(a,pack3(b,c,u))
leaf(tag,args) = pair(1,pair(tag,pack(args)))
```

The imported definitions are `pack2Value`, `pack3Value`, `pack4Value` and
`leafCertificate` in [MPGen.lean](../../../jamesyc-upstream/pa196/PA196/Arithmetic/Certificates/MPGen.lean)
and [Leaves.lean](../../../jamesyc-upstream/pa196/PA196/Arithmetic/Certificates/Leaves.lean).
In particular, the checker has a very small concrete certificate of formula
zero: `truth = leaf(8,0,0,0,0) = 739`. Its tree is 36, the payload is zero,
the `rho8` domination condition is `0 <= 0`, and `rho8(0,0,0,0) = 0`.
The imported `Certificates.verify_r8` theorem therefore supplies
`verifyValue(739) = 1` after these elementary calculations. This provides the
fixed truth proof needed for initial store, guarded gate, failed MP, and
numeric stack underflow; it does not use semantic truth or PA consistency.

## Concrete command updates

Let a nonhalting store have numeric fields `(t,w,d,h)` and certificates
`(pt,pw,ph)`, with `verifyValue(pt)=t+1`, `verifyValue(ph)=h+1`, and the
[parallel-stack invariant](../README.md). Write `gen(v,p)` for the imported
`genCertificate v p` and `mp(b,p,q)` for `mpCertificate b p q`.

* **Shift:** if `t+h=1`, return `pt` if `t=1` and otherwise `ph`; its accepted
  formula is 1. Otherwise use `ph` as the new top certificate and the
  conditional stack-pop operation for the new head and stack certificates.
  In the underflow case use the fixed 739 certificate. The numeric transition
  is exactly that of [Store.lean](../../../jamesyc-upstream/pa196/PA196/Commands/Store.lean).
* **MP(x):** let `y=d+x`. On the successful branch `Code.I(t,y)=h`, use
  `mp(y,pt,ph)` as the new top certificate, `truth` as the new head, and
  `pair(truth,pw)` as the new certificate stack. The imported
  `Certificates.verify_mp` checks this construction uniformly in every PA
  model, including the case `Code.I(0,0)=0`. On failure, use `truth` for
  both displayed formulas and retain `pw`.
* **AX(c,x,y):** let `D=d+x`, `H=h+y`, `A=c`. Push the following proof codes
  in the displayed top-to-bottom order, using the same `foldr pair` as the
  numeric stack, followed by the previous `pt`:

  | Numeric head | Certificate |
  | --- | --- |
  | `head6(D,A,H)` | `leaf(7,D,A,H)` |
  | `head5(D,H)` | `leaf(6,D,H)` |
  | `head4(D,A,H)` | `leaf(5,D,A,H)` |
  | `head3(D,A,H)` | `leaf(4,D,A,H)` |
  | `head2(D,A,H)` | `leaf(3,D,A,H)` |
  | `head1(D,H)` | `leaf(2,D,H)` |
  | `rho8(D,A,H,d)` | `leaf(8,D,A,H,d)` |
  | `U(d,h)` | `gen(d,ph)` |

  `Certificates.verify_head1` through `verify_head6`, `verify_r8`, and
  `verify_gen` give the corresponding all-model checker equations. The
  `verify_r8` premise is `d <= D`, immediate from `D=d+x`.
  For the new top use `truth` if `A=H` or `A=D`, and otherwise use
  `leaf(9,H,D,A)`; `Certificates.verify_bundle` handles the latter with
  premises `A != H` and `A != D`. The new head certificate is `truth`.

The head theorems' conclusions use the internal expression evaluator
`ActualArithmeticGraph.eval`; [HeadGraphs.lean](../../../jamesyc-upstream/pa196/PA196/Arithmetic/HeadGraphs.lean)
contains the corresponding standard-Nat `head*_exact`, `rho8_exact`, and
`bundle_exact` identities and all-model expression-graph totality. The
model-level command representation must use and verify the same expressions;
standard-Nat identities alone do not establish agreement for nonstandard
codes.

## Available definability and remaining work

`M6.PA.SourceCantorInternal` has IΣ₁ definability instances for `pairValue`,
`decodeLeft`, and `decodeRight` in
[SourceCantorDecodeInvariant.lean](../../../jamesyc-upstream/pa196/M6PA/Scheduler/SourceCantorDecodeInvariant.lean).
The `pack`, `leaf`, `mpCertificate`, and `genCertificate` definitions are
finite compositions of these functions and addition; deriving explicit
representations/instances for those compositions is still required where an
internal induction invokes them. The source defines `Checker.verifyGraph`
and proves `verify_graph` and `verify_total_unique`, although this inventory
has not found a named `verifyValue` definability instance. The generic
expression graph and its totality cover the arithmetic head expressions.

The imported `verify_head*`, `verify_r8`, and `verify_bundle` are stated over
arbitrary IΣ₁ models; `verify_mp` and `verify_gen` are stated in the PA-model
section. These are Lean theorems **about all models**, not standalone exported
PA sentences for the full command invariant. The present workspace has not
rebuilt the imported Lean 4.35 project. To obtain the needed internal result,
one must still represent the full annotated store, the source-level command
step and finite command history, and the bounded certificate-stack invariant;
prove their update and induction in PA for arbitrary model-length histories;
bind a literal machine halting trace to a command halt; and translate an
accepted formula-1 checker certificate into a PA refutation. The existing
checker constructors do not themselves prove those global statements.

## Finite controls

From the repository root, `python3 -B
Computability/BusyBeaver/Research/PA/pa196-vs-u208/reverse-cert-stack/imported-checker/replay.py`
checks the source SHA-256 pins, the literal truth certificate, one GEN and one
MP certificate, both gate cases, all eight AX head positions for five small
inputs, and rejection of zero fuel, failed guards, and a mismatched MP premise. The script evaluates
only the needed entries of the checker table by the fuel recurrence and the
imported `CheckerRows.rows_nth` equation; it does not allocate a table with one
entry per enormous tree code. It is a Python transcription with finite
examples, not a replacement for the imported theorems or a PA proof.

### Corrected head-order transcription

An earlier version of this prototype passed `(H,D,A)` to heads 3 and 4.
That was wrong: the imported `Code.heads D H A d h` calls both with
`(D,A,H)`. Its finite checker examples originally repeated the same permutation
on the formula and certificate sides, so those controls did not detect it.
The prototype and its receipts now use the upstream order.

The independently kernel-checked [upstream command audit](../UpstreamCommandAudit.lean)
imports the actual pinned PA196 `Commands.Code` and `Commands.Store` files.
For `D=1,H=0,A=0`, it verifies that the real fourth-head code is `144136`,
whereas the earlier permutation gives `119544`. It also proves that the
standalone Lean command formulas and store step agree with the imported ones.
The checker constructor interfaces remain hypotheses; this audit is not an
internal iPRA theorem.
