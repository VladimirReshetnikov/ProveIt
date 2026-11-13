# A bounded certificate invariant for the PA196 stack

The PA196 numeric stack uses the Cantor encoding `pair(0,0) = 0`. Thus a
zero formula pushed onto an empty numeric stack is indistinguishable from an
empty stack. A reverse proof-transport argument can handle this alias with a
parallel certificate stack whose entries beyond numeric underflow are ignored.
The observation below is a mathematical lemma about the encoding; it does
not establish the PA196 reverse consistency implication.

Let `decode` be the inverse of `pair`, with `decode(0) = (0,0)`, and let
`walk(x,i)` apply the second component of `decode` to `x`, `i` times. For a
numeric stack `w`, a certificate stack `p`, and a relation `Cert(proof,formula)`,
define `Good(w,p)` to mean that, for every `i`, whenever `walk(w,i) != 0`,
the first component of `decode(walk(p,i))` certifies the first component of
`decode(walk(w,i))`. In particular, `Good(0,p)` holds for every `p`: once the
numeric stack is zero it remains zero, and all later certificate entries are
ghosts.

Suppose `Good(w,p)` and `Cert(q,a)`. Then
`Good(pair(a,w),pair(q,p))`: at index zero the two decoded heads are `a` and
`q`; at every later index the decoded tails are the original stacks, so the
old invariant applies. When `pair(a,w) = 0`, the new invariant is vacuous;
no assumption about the ghost certificate stack is needed.

For a pop, if `w != 0`, return the head of `p` and advance both stacks to their
decoded tails. The invariant at index zero certifies the returned numeric head,
and the remaining obligations follow by shifting the old index by one. If
`w = 0`, return a fixed certificate of formula zero and leave `p` unchanged.
The numeric decoder returns head and tail zero, and `Good(0,p)` still holds.
For example, a push of numeric zero onto numeric zero, paired with a ghost
certificate stack headed by 42, has numeric code zero and certificate code
`pair(42,0) = 903`; underflow returns the fixed truth certificate, not 42.

For the PA196 pairing `pair(a,b) = triangle(a+b) + b`, the second component of
`decode(w)` is strictly less than `w` whenever `w > 0`. Indeed, if
`w = pair(a,b) > 0`, then `a+b > 0`, so `triangle(a+b) > 0` and `b < w`.
Consequently `walk(w,i) = 0` for every `i >= w`, by induction. The apparently
unbounded `Good(w,p)` is therefore equivalent to checking the displayed
condition only for `i < w`. The exact pairing and decoder are defined in the
imported [Cantor source](../../jamesyc-upstream/pa196/M6/Source/Cantor.lean).

A PA-internal proof still needs a primitive-recursive checker proof predicate,
representations of bounded walking, pairing, and conditional pop in the chosen
arithmetic language, and proofs in PA of these preservation statements and
induction for arbitrary, including nonstandard, codes. It also needs
proof-producing updates for every command, a connection to PA196's actual
checker, translation of accepted derivations into PA proofs, and extraction of
an appropriate command run from an arbitrary model-length halting trace. None
of those end-to-end obligations is discharged by this lemma.

## Lean prerequisite for the command extractor

[CertificateStack.lean](CertificateStack.lean) kernel-checks the bounded
numeric/ghost-certificate stack invariant for the exact PA196 Cantor pairing,
including the `pair(0,0)=0` alias. Its `Commands` namespace defines the Shift, MP and AX numeric store update
shapes; the AX `heads` and `gate` numeric functions are parameters rather
than imported PA196 definitions. Given explicit assumptions for the native
checker's truth, modus-ponens, AX-head and gate constructors, it proves
that each update preserves the certificate invariant and defines a
deterministic extractor whose returned certificate checks formula 1 whenever
a finite command word halts from a sound store. The initial zero-store case is
also stated. The AX head certificates are checked in stack order by an
inductive aligned-list predicate.

Run from the repository root:

```sh
lean Computability/BusyBeaver/Research/PA/pa196-vs-u208/reverse-cert-stack/CertificateStack.lean
```

On Lean 4.32, the printed theorems depend on `propext` and `Quot.sound`, with
no `sorryAx`. This is an ordinary-natural-number theorem with conditional
checker-constructor hypotheses, not a theorem of iPRA, not an instantiation of
the exact imported checker, and not a PA196 tape-machine halt theorem. The
constructor hypotheses must be connected to the native checker in the chosen
object theory, and the source, physical, and proof-translation bridges must
still be established internally.

[UpstreamCommandAudit.lean](UpstreamCommandAudit.lean) imports the actual
pinned upstream Cantor, command-code, and command-store definitions, proves
that the standalone definitions agree with them for all inputs, and derives
the conditional certificate result for a word of actual upstream commands.
It also proves a concrete counterexample to the previous head-3/head-4
parameter ordering. From the repository root, run:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/reverse-cert-stack/check_upstream.py
```

The tiny Lean build uses a private temporary directory; its deterministic
output is [upstream-command-audit-receipt.json](upstream-command-audit-receipt.json). The actual native checker equations remain explicit
hypotheses, and this is still not an iPRA derivation.

## Direct numerical checker

[NativeChecker.lean](NativeChecker.lean) implements the numeric checker-rule
and fuel recurrence directly on natural numbers. It proves the truth, six head,
restricted propositional, bundle, modus-ponens and generalization certificate
interfaces, including a constructive accepted-entry fuel/bound monotonicity
lemma. It also proves that the entry recurrence agrees with an explicit finite
list-table construction. [NativeCheckerBinding.lean](NativeCheckerBinding.lean)
therefore obtains a checker-accepted code 1 from an actual imported PA196
command word that halts from the zero store, with no checker-correctness
hypotheses. These are standard-natural-number theorems, not iPRA theorems.

[CheckerRuleSyntax.lean](CheckerRuleSyntax.lean) contains source fragments
extracted byte-for-byte from the pinned upstream arithmetic-expression, head,
scalar-expression, and checker-rule definitions. Its separate callback
interpreter handles the preceding table through a function `Nat → Nat`; this
specialization applies to the checker rule because its only two uses of the
preceding table are `nth` operations. [CheckerRuleAudit.lean](CheckerRuleAudit.lean)
proves that this interpretation of the extracted rule agrees with the direct
numeric rule on all inputs. The fragment check and full Lean build run with:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/reverse-cert-stack/check_native_checker.py
```

The deterministic output is [native-checker-receipt.json](native-checker-receipt.json).
The printed results use `propext` and `Quot.sound`, with neither `sorryAx` nor
`Classical.choice`. The direct finite-list table has **not** been formally
identified with the imported Foundation HFS/model-valued `Checker.verifyValue`.
That connection, the literal-machine halt extraction, and iPRA-internalization
are still required for the target equivalence.
