# Heterogeneous alphabets improve the composed polynomial-space certificate

Prepared for parent /root. This is a proof memorandum, not a claim of a new
logarithmic order and not an end-to-end SAT implementation.

## 1. Result and exact dependency boundary

For the same normalized Boolean tensor interface as the asymmetric incoming
packet (root at most s wires, degree at most ceil(s^(9/10)), initial precision
and truncation O(s), entries evaluable in poly(s+L) exp(O(s^(9/10)))), combine:

1. the preprint's exact deformation, recovery, immutable creation-time lifts,
   child factorization, and polynomial-space traversal;
2. the asymmetric packet's deterministic two-stage balancing, fresh-side
   degree invariant, exact unequal-symbol fraction, and additive precision gap;
3. the joint-Cauchy packet's full-orientation group-preserving modes, with
   uniform asymptotic weight slope 4 and the same family multiplicity.

Changing only the alphabet and retained-range schedule gives the new bound

    poly(s+L) * 2^((C_het+o(1))*s/sqrt(log2 s)),
    C_het = 63.85220339054881272668715341378...

with polynomial working space. This assumes the unchanged upstream algebraic
architecture and the compatible full-Cauchy lemma; it is an ordinary
mathematical proof, not a new proof-assistant certificate. It is not a
constant per SAT variable. SAT width and reduction constants still apply.

The novelty is the explicit multi-stage capacity allocation combining the
asymmetric degree invariant with several changes of alphabet. The separate
round-2 incoming packet already changes the root alphabet relative to its
tail, so changing the number of groups by itself is not a new idea. The
packet labels are fresh at every call; no identity requires the same alphabet at different depths.
Only the cumulative packet exponent a_d carries precision history. Existing
tensor descriptions are retained unchanged, and changing the next call's
label alphabet does not change their defining entries or lifts.

The exact asymmetric count ALREADY contains 1-1/r. It must not be applied
twice when composing with the round-2 packet.

## 2. The inherited local estimates

Let lambda=ceil(log2 s), active cutoff H=ceil(s/lambda), h=lambda (or max(2,lambda)),
packet length L_d=2^a_d, alphabet r_d, and full label count Q_d=r_d^a_d.

At the root both side degrees are bounded by Delta=ceil(s^.9). Below the root,
retain all old vertices on the row side and all fresh packet vertices on the
column side. The degrees satisfy R_d<=Delta and C_d<=2L_(d-1).

The exact asymmetric packing lemma implies near-unit padded mass P/M=1+o(1)
whenever, uniformly over active calls,

    Q R/M=o(1),
    Q^2 C (log s)^2/M=o(1),
    L Q^2/M=o(1).

Its explicit relative error is O(1/lambda) plus fixed-power vanishing terms
under the schedule below. Therefore the product of padding factors across
O(log lambda) levels is 1+o(1), not merely a depth-wise unspecified o(1).

Each child has at most (2/r_d)(1+o(1))M wires. At retained valuation i,
D=2^(a_d-i), the number of mode families is

    c_i <= (2(1-1/r_d)+o(1)) M/D.

The sharp taper and additive buffer give working precision

    p_i <= (6+o(1)) MD/u_d.

For weight slope 4, the generating-function entropy is

    sum_j -ln(1-exp(-theta*w_j)) <= (pi^2/24+o(1))/theta.

Using the displayed family and precision envelopes, and optimizing theta,

    ln N_i <= (kappa(r_d)+o(1)) M/sqrt(u_d),
    kappa(r) = pi sqrt(2(1-1/r)).

Derivation: 2 sqrt[p*c*pi^2/24] equals
pi sqrt(2(1-1/r)) M/sqrt(u). The changing alphabet ranges over the finite set
{4,6,8,13,14}, so the error can be taken uniformly over it.

## 3. A strictly feasible rational schedule

Take alphabets

    r_0=13, r_1=14, r_2=8, r_3=6, r_d=4 (d>=4).

Define eta_d by

    eta_0 = 27/2000,
    eta_1 = 51/4000,
    eta_2 = 141/20000,
    eta_3 = 107/20000,
    eta_d = (27/6400)*(5/8)^(d-4), d>=4.

Set u_d=floor(eta_d*lambda), b=6 ceil(log2 lambda), and

    a_d = sum_(j=0)^d u_j + (d+1)b.

The rational geometric sequence is computable by integer arithmetic. It is
not necessary to compute irrational logarithms to select any schedule value.
The cumulative leading capacities are

| depth | sum_(j<=d) eta_j | alphabet |
|---|---:|---:|
| 0 | 27/2000 = .0135 | 13 |
| 1 | 21/800 = .02625 | 14 |
| 2 | 333/10000 = .0333 | 8 |
| 3 | 773/20000 = .03865 | 6 |
| all tail depths | at most 499/10000 = .0499 | 4 |

The root needs 2 a_0 log2(r_0) < .1 lambda at leading order; every later
depth needs a_d log2(r_d) < .1 lambda. All these are STRICT inequalities,
certified without floating point by

    13^27 < 2^100,
    14^21 < 2^80,
    999 < 1000,
    6^773 < 2^2000,
    998 < 1000.

For example, the first is equivalent to
2*(27/2000)*log2(13)<1/10, and the fourth to
(773/20000)*log2(6)<1/10.

Thus the root has Q_0^2 Delta <= s^(1-epsilon+o(1)) for a fixed epsilon>0.
Below the root Q_d R_d has the same kind of fixed exponent gap. Also

    2(a_d/lambda)log2(r_d) + a_(d-1)/lambda
        < 1/5 + 499/10000 = 2499/10000 < 1,

so Q_d^2 C_d=o(M/polylog(s)). Rounding has the same upper power because

    (a_d/lambda)(1+2log2 r_d) < 2499/10000.

The maximum new tensor degree is at most 2L_d=s^(.0499+o(1))<<s^.9.
The original maximum-degree invariant therefore persists. The additive
buffers contribute O((log lambda)^2)=o(lambda) and cannot consume a fixed
power gap. Floors only lower a_d.

## 4. Depth bootstrap, minimum retained range, and precision

Prove the preceding bounds first for all hypothetical depths

    d <= ceil(log_(5/3) lambda)+C

and active M>H. Uniformly there, a_d<=.0499 lambda+O((log lambda)^2), and

    u_d >= lambda^(epsilon_0+o(1)),
    epsilon_0 = 1 - ln(8/5)/ln(5/3) > 0.

The positivity follows from 8/5<5/3, or equivalently 24<25. The numerical
epsilon_0 is about .080. Floors are therefore a vanishing relative error.
The fixed root/prefix levels do not affect this lower bound.

All packing gates hold uniformly in the hypothetical range. Each child has
at most (2/r_d)(1+o(1))M <= (1/2+o(1))M, eventually at most 3M/5.
Thus an active path cannot exceed the displayed depth range. This closes the
induction without assuming a shrinkage guarantee before proving the gates.

The root/prefix exact shrinkage factors are

    f_0=1, f_1=2/13, f_2=2/91, f_3=1/182,
    f_d=(1/546)*2^(-(d-4)), d>=4.

The product of padding errors is 1+o(1), hence M_d<=(1+o(1))s f_d.

For inherited precision, use the asymmetric packet's elementary proof:
p<=O(s lambda^2 2^a_(d-1)). The least retained D is at least
2^(a_(d-1)+b+1). Since s/M<=lambda and u_d<=lambda,

    p / (MD/u_d) = O(lambda^4 2^(-b)) = O(lambda^(-2))=o(1).

The extra jet-evaluation loss rho*u_d*(a_d+1) is likewise o(MD/u_d), while
rho=(1+o(1))M/u_d. This proves p_i<=(6+o(1))MD/u_d uniformly.
In particular D>=lambda^6 at every active call, so the entropy saddle
theta asymptotic to sqrt(u_d)/D tends uniformly to zero. Positive offsets
in the full-Cauchy weights may simply be dropped for this upper bound.

## 5. Exact coefficient and remaining costs

Let kappa(r)=pi sqrt(2(1-1/r)). The leading coefficient is

    C_het = 1/ln2 * [
      kappa(13)/sqrt(27/2000)
      +(2/13) kappa(14)/sqrt(51/4000)
      +(2/91) kappa(8)/sqrt(141/20000)
      +(1/182) kappa(6)/sqrt(107/20000)
      +(1/546) kappa(4)/sqrt(27/6400) / (1-sqrt(2/5))
    ].

The tail denominator is correct because its size shrinks by 1/2 and u by
5/8, giving work ratio (1/2)/sqrt(5/8)=sqrt(2/5)<1. This geometric series
also makes summing the uniform entropy and shrinkage errors harmless.

Exact rational interval arithmetic certifies

    63.85220339054 < C_het < 63.85220339056.

The verification script uses Machin's formula with alternating rational
arctangent bounds for pi, the positive atanh series for ln 2, and integer
square-root brackets. It does not use a floating-point optimizer to certify
the theorem. A separate exploratory optimizer motivated the schedule but
is not part of its proof.

Polynomial multiplicities for interpolation nodes, values, and child groups
over O(log lambda) levels contribute O(lambda log lambda) to log time.
Direct leaves contribute O(s/lambda), original entry routines O(s^.9), and
new packet-entry evaluations O(L_d log s)=s^(.0499+o(1)); all are
o(s/sqrt(lambda)). Arithmetic, graph data, and immutable tensor descriptions
have polynomial sizes because a_d=O(lambda), labels and precision are
polynomial in s, and the alphabet is bounded by 14. Depth-first traversal
uses polynomial space. The input description-length factor stays a fixed
polynomial, as in the inherited proof.

## 6. Comparison and qualified novelty

The asymmetric packet's 76.9089949516 polynomial-space coefficient already
contains exact crossing fraction. Composing it with joint-Cauchy slope 4
gives 76.9089949516*sqrt(3/4)=66.6051434... . Merely taking its fixed-r=16
capacity boundary gives 66.1927236936; the present rational heterogeneous
schedule improves even that stronger comparison to 63.8522033905.

This is a quantitative upper-bound improvement; it is not a measured SAT
runtime ratio or a new n-only logarithmic order. A separate cached/Strassen
contraction from the joint packet uses more space and may have a smaller
time coefficient; comparisons must separate the polynomial-space and
exponential-space frontiers. Neither frontier dominates unproved conditional
n/log n target interfaces, which are not established algorithms.

## 7. Four assigned incoming archives: review summary

Paths below are relative to incoming_extracted. All are from ProveIt pin
ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06.

* eth_asymmetric_packet_balancing_2026-10-26/.../report.tex: pair balancing
  theorem starts line 311, load bound 318, padding gates 386, exact crossing
  fraction 438, fresh-side degree invariant 450, sharp precision 526,
  factorial entropy 554, and fixed-r=16 schedule 563-569. Main coefficient
  76.909, low-degree coefficient31.0641. Strongest of my assigned four for
  the full original interface. Its annulus slopes approach3 uniformly and
  do not supply the stronger full-Cauchy4 gain.
* eth_balanced_packing_2026-10-26/eth_balanced_packing/report.tex: coefficient
  94.7482022595 at line63; two-stage balancing is polynomial time and reaches
  near-unit common padding under symmetric degree conditions; modes use
  multiplicity2M/D at lines450-475, omitting unequal-symbol savings. Its
  `code/packing.py` recomputes full conditional expectations at each candidate.
* eth_high_moment_2026-10-26/.../report.tex: coefficient94.7482022595 at
  lines39-44. Moment proof153-209 is coherent: dependency via matchings,
  Holder mgf, even moment potential; growing t=lambda costs exp(O(lambda²))
  and polynomial space, explicitly paid as lower-order setup. Its polynomial
  orbit-padding alternative247-291 gives98.8967. These have weaker root and
  tail degree budgets than the asymmetric schedule. Code is exact component
  checking, not SAT benchmarking.
* eth_recursive_refinement_2026-10-26/eth_recursive_refinement/report.tex:
  coefficient133.20737249245 (macroline39; theorem98). kernel.tex derives
  uniform slope64/21 (lines260-276), compatible with asymmetric scheduling
  but superseded by the joint packet's4 slope. It explicitly records that
  finite inventories need not improve pointwise. Its finite comparison and
  absence of a new unrestricted logarithmic order are accurately qualified.

I found no concrete mathematical counterexample in the four audited new
local lemmas. I did not rebuild the full SAT reduction or run these entire
archived packages; the new exact schedule arithmetic was run normally and
under python -O with byte-identical JSON results. The reference algorithms
are useful objects for a practical incremental-potential optimization,
which the incoming_practical agent is now implementing against the fastest
asymmetric reference, not only the older slower balanced reference.
