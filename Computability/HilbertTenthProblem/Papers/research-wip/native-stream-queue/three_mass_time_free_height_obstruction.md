# Removing time from the height admits false clocks

**The one-addition deletion is unsound for the maintained inc2/dec2 source.** Its true raw triple `(x,y,T)=(0,1,616)` acquires a complete positive-witness zero at `(0,1,137438954087)`. Every native witness can be kept unchanged. This refutes the deletion as a uniform rule for the four clock circuits; it is not a false-input or universality claim.

The [pinned checker](three_mass_time_free_height_obstruction.py) reads the complete maintained [target-free-height packet](three_mass_target_free_height.md), verifies its actual consumers and emits the four literal syntactic proposals in its [receipt](three_mass_time_free_height_obstruction.json). It executes no historical Python, author verifier or huge native Pell construction. The three one-step examples have a different conclusion, explained below; they are not refuted by the incdec example.

## Literal deletion and full polynomial identities

The maintained height is `h=n0+eta+T`, implemented by two additions. Deleting the private first height register and defining the existing final height register as `n0+eta` saves one addition. The target, all 19 comparisons, every witness and the entire SOS finalizer are retained. The syntactic complete totals are 591/466/464/467, in incdec/zero3/nop/positive3 order; their respective M+A counts are 235+356, 180+286, 178+286 and 185+282. These are paid source counts, not a claim that all four preserve their represented clock relations. Degree remains bounded by 2344/1192/1192/1192; no exact-degree claim is made.

The independent source scans find precisely two maintained consumers of `T`: the final height addition and the clock right side. After the deletion, only the latter remains. The positive `clock_quotient_hat` has one private consumer, its subtraction of one, followed by the product with the actual `B-1`. The retained clock equation is exactly

\[
 C_\tau=(B-1)(\widehat Q-1)+T.
\]

The proposed complete polynomial has an all-value signed identity with the maintained parent at `eta_parent=eta-T`. Separately, since the new height and therefore `B` are independent of `T` and `Qhat`, the substitution

\[
 T'=T+(B-1),\qquad \widehat Q'=\widehat Q-1
\]

preserves the **entire proposed polynomial**. The sole affected comparison operand agrees by the exact coefficient identity

\[
 (B-1)(\widehat Q-2)+T+(B-1)
 =(B-1)(\widehat Q-1)+T.
\]

The checker expands this identity in independent atoms `B-1,Qhat,T`, authenticates the literal source cone implementing it, and then checks the complete downstream graph and finalizer. Every other comparison and every native port stays unchanged. The shift is positive on the declared natural/positive domain whenever `Qhat>=2`.

## Why every genuine multistep clock supplies margin

For a genuine accepting path of length `t`, with positive ticks `tau_i`, the canonical quotient is

\[
 Q=\frac{\sum_{i<t}\tau_iB^i-\sum_{i<t}\tau_i}{B-1}
 =\sum_{i=1}^{t-1}\tau_i(1+B+\cdots+B^{i-1}).
\]

For `t>=2` this is positive, so `Qhat=Q+1>=2`. Choose any valid prescribed height large enough for the genuine path and its true clock in the maintained construction. Replace its height slack by `eta=eta_parent+T`; the proposed source has the same height, radix and native inputs, and a genuine complete positive zero. The displayed clock shift then gives another complete positive zero with strictly larger, incorrect requested time. All native witnesses from the genuine zero are copied unchanged.

This is a general obstruction within this exact clock/height scheme for any fixed source having an accepted path of length at least two. It needs no universal machine theorem. Its hypothesis is a genuine accepting path and the inherited prescribed native-extension theorem, not merely a modular outer assignment.

## The actual incdec witness

For the fixed maintained inc2/dec2 table, raw input `x=0` means mass 1. The actual encoded numeric path is

\[
 1\longrightarrow7\longrightarrow3,
\]

representing initial mass 1, intermediate mass 2, and halt at mass `y=1`. Both literal table transitions use quotient zero and take 308 physical ticks; the true time is exactly `L=616`.

Set `h=1024` and choose the maintained target-free parent slack `eta_parent=407`, so `h=1+616+407`. This is an admissible prescribed height: it exceeds `n0+L=617` and every current-state quotient. The new time-free slack is `eta=1023`. The actual paid radix multiplier is `131072`, hence

\[
 B=131072\cdot1024^2=2^{37}=137438953472.
\]

The two selector words are `E_1=1` and `E_7=B`; all other selectors and all quotient/product words are zero before positive hatting. Thus `J=1+B`, `P=B^2`, and the actual global slack is `B^2-B-4>0`. The computed clock word is `308+308B`. Its canonical quotient is 308 and its positive hat is 309.

The shift gives

\[
 T'=616+(B-1)=137438954087,\qquad \widehat Q'=308>0.
\]

All other supplied coordinates, including `eta=1023`, and all native coordinates remain unchanged. The clock equality, both other outer equalities and the complete joined AND are identical. The inherited native theorem supplies positive witnesses for this actual dyadic prescribed scale and genuine joined-AND data. Consequently every comparison of the complete proposed source is zero, and its SOS output is zero, at the false time `T'`.

The finite receipt constructs the actual outer data at the maintained seed and at shifts `k=0,1,2,307,308`, with

\[
 T_k=616+k(B-1),\qquad \widehat Q_k=309-k.
\]

The formula proves positivity for every `0<=k<=308`, so this fixed native witness fiber contains 308 false requested times. The finite check does not materialize the native Pell witnesses; their existence follows from the pinned completeness theorem at the valid seed height, and the exact complete-source identity preserves them afterward. This distinction is essential to the full-zero conclusion.

## The three exactly-one-step sources are different

The actual zero3, nop and positive3 tables send initial-state rows directly to halt or trap. Every noninitial state goes to trap, including halt itself. Their slopes are all 30, divisible by the control modulus 5, so these control destinations do not depend on the residue quotient. Hence every accepted chronology has exactly one transition.

For those sources, `Ctau=tau_0<B-1`. Natural `T` and positive `Qhat` in the unchanged clock equation force `Qhat=1` and `T=tau_0`, even without `T<h`. The clock-shift identity still holds algebraically, but its seed hat is only 1; increasing `T` by the modulus would make the hat zero and leave the positive domain. Thus the present obstruction does not refute the three one-step deletions. Their maintained source/API implementation and separate proof audit are a different packet; no such API is provided here.

## Scope and replay

The receipt contains four literal proposal schedules, four complete signed height identities, four complete clock-shift identities, all 76 retained comparisons, all 1,988 paid live gates and unchanged full finalizers. It also checks 64 exact complete numerical identities, including eight rational cases, and five genuine outer fiber points. All fifteen predecessor source/proof/receipt files are authenticated before use. The helper is a research CLI with no public unsafe compiler API.

Only the standard library is needed. From any working directory:

```sh
python /tmp/three_mass_time_free_height_obstruction.py \
  --root /home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue \
  --expect /tmp/three_mass_time_free_height_obstruction.json
```

Initial generation and a fresh exact typed replay from `/` pass. No repository or frozen parent was modified. The conclusion concerns preservation of the raw exact-clock relation by this literal deletion; it states neither a new universal bound nor a general arithmetic lower bound.
