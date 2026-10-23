# Independent review of the B4 source adapter

## Verdict

**PASS. No gap was found in the new source-coding argument, its composition
interface, or the advertised degree and operation count.** The ten-integer
result retains the explicitly stated dependencies on the inherited native
compiler/K215 endpoint, the parent quartic, and Sun's arithmetic bridge. This
review is not a new end-to-end proof-assistant certificate or a reproof of all
the Lucas-sequence theorems in the cited preprint.

The reviewed main circuit is `ten_integer/generated/b4_signed10.json`, SHA-256
`eecb86780bd7aeaeb40a2b7de2906b35731a350a75e298fa440e46b022d7fb21`.
The independent auditor in this directory imports no builder or verifier code.
It reads the actual fixed coefficient payloads, evaluates the literal weighted
coefficient recipes, and independently checks the final JSON circuit.

## 1. What is actually needed of the additive code

For the source polynomial of degree four, unique sums of four code elements,
with repetition allowed, imply injectivity of

    alpha -> sum alpha_i w_i

on every multi-index of total degree at most four: pad to length four with
the unique zero code element. No superincreasing condition is needed. The
review independently enumerated all 52,360 four-element multisets from the
32 displayed weights. Their sums are distinct as integers and modulo 1,048,575.
The largest weight is 942,302. This finite certificate suffices independently
of the finite-field construction explaining where the list came from.

For completeness, the finite-field explanation is logically sound as stated.
If the residue class theta has order 2^20-1 in the binary quotient of dimension
20, its powers exhaust all nonzero classes, making every such class a unit.
The quotient is therefore a field without a separate irreducibility assumption.
A primitive element has degree four over its 32-element subfield. Equal
fourfold products of theta+c reduce, after cancelling the monic leading terms,
to a polynomial relation of degree at most three; such a relation must vanish
identically. Translation of the discrete logarithms preserves four-sum
uniqueness.

The 31 positive weights are assigned to the 31 existing source witnesses.
The zero weight homogenizes the fourth power; it is not an additional
existential witness or a varying input digit.

## 2. Exact coefficient recovery

Put T=max w_i and Lc=4T. Each exponent Lc-alpha.w is nonnegative. The B4
property makes the exponents for distinct alpha distinct. With

    c_alpha=(4-|alpha|)! product(alpha_i!) p_alpha,
    D(t)=sum c_alpha t^(Lc-alpha.w),

the coefficient of t^Lc in

    (1+sum n_i t^w_i)^4 D(t)

is exactly 24 P0(n). A matching product term must have beta.w=alpha.w;
injectivity forces beta=alpha and the factorial factors cancel. This is a
polynomial coefficient identity, not a heuristic about separated large numbers.

The coefficient bound is also correctly adapted. Every coefficient of D has
absolute value at most 24H. The nonnegative coefficients of the fourth power
sum to (1+sum n_i)^4. Consequently every product coefficient has absolute
value at most 24H(1+sum n_i)^4, and the product's degree is at most 8T.
There is no missing combinatorial factor: the convolution is bounded by the
sum of the coefficients of the fourth power, not by the number of source
monomials times that sum.

## 3. Positivity and the shorter upper block

This is the most consequential size check. Under the reverse-bridge size
hypotheses, b=1+3f is a nonzero square and f is nonzero. Hence f>0 and b>=4.
The fixed coefficient bound gives

    B > 2 + 2*24H*(32b)^4.

The constant coefficient P0(0) is positive. Therefore D(B)'s leading term is
24P0(0) B^(4T), while the entire absolute lower-degree tail is bounded by

    24H (B^(4T)-1)/(B-1) < B^(4T).

Thus D(B)>0 before decoding g and before assuming any norm equation. The same
geometric estimate gives

    D(B) < 24H B^(4T+1)/(B-1).

For 0<=g<2 Ccap=2b B^T, one has 1+g<=2b B^T and in particular
1+g<=32b B^T. Therefore

    2(1+g)^4 D(B)
      < (B-2) B^(8T+1)/(B-1).

The added geometric sum is strictly below
B*B^(8T+1)/(B-1). Adding these inequalities yields

    0 < Jcode < 2 B^(8T+1) < N1,
    N1 = 4 B^(8T+1).

Also g<N0=B^(T+1), because B>=2b. Hence
Scode=g+Jcode*N0 is strictly below N=N0*N1. The target block Tcode is
likewise below N. The smaller exponent 8T+1 is therefore sufficient; the
old positional exponent 9T+1 is not needed for this new code.

All these estimates hold on the pre-decoding branch and do not silently assume
the existence of a source zero. They also hold when b is square but has not
yet been shown to be a power of two, as required by the reverse bridge.

## 4. Mask and target-digit decoding

When b is a square power of two, B and all block lengths are powers of two.
The digit mask allows only the low log2(b) bits at the 31 permitted positions.
The bound g<N0 excludes any bits above the coded range. Thus the recovered
digits satisfy 0<=n_i<b, with no additional positional assumption.

The shifted formal product coefficients q_j obey |q_j|<B/2, so
q_j+B/2 are genuine digits strictly between zero and B. The relation
Jcode=2 Jprime is exact. Dividing both tested operands by two in the bitwise
condition is a common bit shift; it does not require a carry-free doubling
inside each radix-B digit. The mask B/2-1 tests the lower bits of the target
digit. Since that digit is in [1,B), it passes precisely when it is B/2,
equivalently q_Lc=0 and P0(n)=0.

The source polynomial has no zero at the all-zero assignment. For any actual
source zero, some n_i is positive, so its code g is at least B and therefore
at least b. Its upper bound is g<Ccap. Choosing arbitrarily large square
powers b=4^s makes f=(b-1)/3 arbitrarily large and integral. This verifies
the cofinality requirement without choosing any unknown source index.

## 5. Imported bridge interface and fixedness

The primary source [Sun 2021](https://arxiv.org/html/1704.03504v7), Lemma 2.2,
has exactly the two-block binomial identity used here when p=P=2. It requires
only power-of-two N and nonnegative Scode,Tcode<N. The new proof supplies
those hypotheses directly.

The relevant source interface and bridge in
[Sun 2026](https://arxiv.org/html/2609.01594v2), Proposition 2.1 and
Propositions 6.1-6.2, use the forward/reverse binomial implications, cofinal
witnesses, the monomial bound Ccap, and the strict size inequalities.
Their subsequent formulas do not inspect the old positional digit weights.
The new Ccap is 2^(4269882*T) b^(4T+1), with fixed positive exponents, and
the new proof establishes the required X>3b and Y>max(b,256). Theorem 4.1
chooses xi divisible by a prescribed positive integer before allowing every
residue class for y modulo xi; this is the quantifier order needed by the
unchanged quintic merger.

The independent DAG inspection found exactly ten variable nodes, with the
advertised ten names, and only literal, fixed, addition, subtraction, and
multiplication nodes otherwise. All fixed leaves resolve to supplied actual
coefficient bytes and finite recipes. Every gate is live. No radical,
division, variable exponent, omitted recursively enumerable index, or
additional existential register occurs in the literal circuit.

The source coefficients remain the complete package-31 tuple. The separately
improved native coefficient tuple is not silently substituted into this circuit.

## 6. Independent circuit and degree certificate

The circuit contains 485 additions, 25 subtractions, and 1,694 multiplications:
2,204 operations in total. Treating every witness as degree one and every fixed
leaf as degree zero gives the independently recomputed upper bound

    degree <= 107286763576.

Substitute a common indeterminate for all ten witnesses. The independent
auditor propagates the coefficient at each gate's degree upper bound, using
the actual coefficient bytes reduced modulo each prime. At the final bound
it obtains:

| Prime | Leading coefficient |
|---:|---:|
| 101 | 16 |
| 1009 | 599 |
| 1000003 | 622356 |

One nonzero value already proves that the upper bound is attained over the
integers. Thus the exact degree is 107286763576. The argument does not infer
degree from random point evaluations or ignore possible intermediate leading
term cancellation: cancellation gives zero at that gate's upper degree and
is carried through the arithmetic.

Separately, 882 named-register comparisons agree between the JSON circuit and
a newly written evaluator of the literal source, bridge, and final norm
formulas. These include signed assignments, f=0, all-zero assignments, and
assignments with B=0 modulo the prime. These comparisons are transcription
diagnostics, not a proof of the universal Diophantine equivalence.

The audit receipt is `B4_INDEPENDENT_AUDIT.json`. The complete proof boundary
remains explicit: the new source adapter and exact finite certificates are
reviewed here; the substantial inherited compiler and Lucas results remain
mathematical dependencies.
