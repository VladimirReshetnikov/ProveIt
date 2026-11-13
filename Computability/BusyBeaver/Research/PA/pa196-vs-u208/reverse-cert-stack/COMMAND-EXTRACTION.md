# Conditional extraction from the PA196 command interpreter

The following construction reduces the command-level extraction problem to
explicit syntactic proof constructors. It uses the numeric store and the
exact three command cases in the imported
[Store.lean](../../jamesyc-upstream/pa196/PA196/Commands/Store.lean). It is a
mathematical construction with stated hypotheses; it is not an implemented
proof checker, a PA derivation, or a bridge from literal Turing-machine
traces.

Let `Cert(p,f)` mean that `p` is a correctly coded derivation of numeric
formula `f` in the exact PA196 calculus. Assume fixed primitive-recursive
constructors, with their correctness verified in PA, for:

1. a proof `truth` of formula 0;
2. given proofs of `a` and `Code.I(a,b)`, a proof of `b`;
3. given `d <= D` and a proof of `h`, proofs of every entry of
   `Code.heads(D,H,A,d,h)` in its actual order; and
4. a proof of `Code.gate(a,b,c)`, including the guard-failure case returning
   formula 0.

These are requirements on a concrete code and checker, not assumptions that
all numeric formulas are true. The constructors must verify the actual
`Code.I`, head, and gate conventions, including the `Code.I(0,0) = 0` alias.

For each numeric store `(t,w,d,h)` retain a certificate triple `(pt,pw,ph)`
with `Cert(pt,t)`, `Cert(ph,h)`, and the bounded stack invariant
[`Good(w,pw)`](README.md). The following updates maintain it:

* **Shift.** If `t+h = 1`, stop and return `pt` when `t=1`, otherwise `ph`.
  One of these cases holds because `t` and `h` are natural numbers, and the
  returned certificate proves formula 1. If `t+h != 1`, the next store is
  `(h, tail(w), d, head(w))`: take the next `pt` to be `ph`, and use the
  conditional stack-pop rule for the next `ph` and `pw`. Numeric underflow
  returns formula 0 and the fixed `truth` certificate.
* **MP(x).** Put `y=d+x`. If `Code.I(t,y)=h`, obtain a certificate for `y`
  by modus ponens, push `truth` onto the certificate stack, and set the new
  `ph` to `truth`, matching numeric store `(y,pair(0,w),y,0)`. Otherwise set
  the new `pt` and `ph` to `truth` and leave `pw` alone, matching
  `(0,w,y,0)`.
* **AX(c,x,y).** Put `D=d+x`, `H=h+y`, and `A=c`. Construct certificates
  for the ordered list `Code.heads(D,H,A,d,h) ++ [t]`, using `ph` for the
  generalized head and `pt` for its final saved top. Push them onto `pw` in
  the same `foldr pair` order as the numeric list. Use a gate certificate as
  the new `pt` and `truth` as the new `ph`, matching the exact AX store.
  The required `d <= D` follows from `D=d+x`.

The stack push and pop obligations follow from the bounded invariant in the
[companion note](README.md), including the `pair(0,0)=0` alias. Starting
with numeric zero store and certificates `(truth, 0, truth)`, induction on a
finite command sequence establishes the invariant at each nonhalting step.
If that sequence reaches the `none` outcome, the exact interpreter has
halted at a Shift, and the update above produces a certificate of formula 1.
No consistency assumption is used in this conditional extraction.

Because the encoders, command updates, and assumed certificate constructors
are primitive recursive, the step-by-step annotated run can be encoded by a
primitive-recursive function. Once the assumed constructor correctness,
stack-invariant preservation, and the code for iteration over finite command
sequences have actually been represented and proved in PA, PA induction can
verify this annotated-run argument also for its nonstandard finite sequence
codes. That internalization is an obligation, not a theorem supplied by this
note. It remains to construct and verify the concrete certificates, bind an
arbitrary model-length **literal machine** halting trace to such a command
sequence, and translate the resulting formula-1 derivation to a PA
refutation. A standard-model run or finite test does not supply those steps.
