# Independent audit of all twelve round-9 nine-variable equations

## Result and scope

The six positive-domain circuits and their six nonnegative-domain translations pass the independent literal audit. The scripts in this directory import no construction program and execute no upstream archive program. They reconstruct the register formulas directly, interpret only fixed `add/sub/mul` DAG nodes, and retain an independent copy of the inherited four-port coefficient binding.

All six positive-domain costs and exact total degrees are:

| Layout | Majorant | Live binary operations | Total degree |
|---|---|---:|---:|
| H2057 | refined | 483 | 1,503,378 |
| H2068 | refined | 481 | 1,510,770 |
| H2082 | refined | 476 | 1,520,178 |
| H2057 | simple | 451 | 1,825,540 |
| H2068 | simple | 449 | 1,834,516 |
| H2082 | simple | 444 | 1,845,940 |

Each natural-domain translation adds seven operations and preserves the degree. Nine free unknowns occur in every circuit. Every node is live, and the graphs are acyclic. Multiplications used by the shared addition chains count as ordinary operations. Fixed integer construction is not counted by this circuit measure; no claim about bit-complexity or shortest printed expression follows.

## Independently checked finite evidence

- All fixed integer gzip payloads, decompressed hashes, signs and bit lengths; all circuit coefficient recipes evaluated over the complete coherent inherited tuple, including `MF_source` rather than the unshifted mask.
- All twelve circuit source and layout pins. The three copied sources are byte-exact; the three kernels are exactly identical to audited carry kernels after the explicit field renaming `powers/coefficient` to `port_powers/integer`. Layouts retain their audited raw hashes. Carry audit provenance is rebound, not silently assumed to apply to a changed source.
- 720 deterministic modular input cases across three primes, including the all-one positive and all-zero nonnegative boundary assignments. Both the output and 39 independently reconstructed registers are compared. Modular sampling corroborates implementation; it is not itself a proof of a universal identity.
- Exact symbolic reconstruction of all 703 coefficients of the refined defect. Its coordinatewise exponent bounds are (15,18,6), attained simultaneously only at the term with coefficient 9 times 2^18. This establishes the weighted-degree leader used in all three source compositions.
- Strict degree comparisons after the norm cancellations. They give refined degree 86r+328nu+4c+260 and simple degree 104r+400nu+8W+316. The positive source leader is 1 in the two unreflected layouts and beta+2 in the reflected layout; neither leader can vanish for the actual coefficient tuple.
- Exact symbolic checks of the rational E7 remainder identity, collected T6, both quotient-division identities, normalized margin, shifted numerator, four-factor norm and simple Pell defect.
- Integer calibration parameters are recomputed, including the parity factor in L. The threshold population identity is checked at five binary exponents, while its displayed linear identity in k proves it uniformly.

## Mathematical review

### Positivity before any decoding hypothesis

In H2068 and H2082, the positive quadratic leader and the certified layer gaps dominate the other two kernels when Us is at least B^W. H2057 is different: every kernel has a positive leading coefficient, respectively 2K0, 2 and beta. Its linear and quadratic source heights tie, so the exact leading source coefficient is beta+2, not beta. The actual coefficient bound M and B greater than 4096M make the geometric-tail bound uniform. No source root or upper bound on g is used to infer Gs>0.

Once the ratio margin yields g<4bB^W, the weaker bound Us<6bB^W is the correct one. The retained signed-carry proof then bounds both words below the calibrated block. At b=1 the low mask forces g=0, excluded by the positive domain. The all-one source tuple is not a source root, so completeness can choose a strictly positive encoded g.

### Parity and threshold

With Ec=H+W+2, Hp=Ec+W+23, delta=(Hp-15) mod 2, and lp=(22-Hp*kappa) mod 2, set

    eN=(Hp-15-delta)/2,
    e2=((15+delta)kappa+lp-22)/2.

For v=kappa+2k, the exact identity

    lp+k+Ec*v+(W+23)*v-31*k-22
      =2*(e2+delta*k+eN*v)

holds by substitution, not asymptotics. The lp factor is necessary in the even-height layouts. The nine-variable construction uses N itself as the ratio threshold, not the larger block L.

### Margin first, integrality second

The new m is one eighth of the inherited ratio margin. The identity

    E0=Jn+(J-2)(bw)^2+3bwC+2>0

holds even when Q is negative. Both majorants are unconditional. The real factorization of the norm therefore forces m>0 before any square-integrality inference. If m=0, the norm is E0^4, never zero.

The recovered margin yields C>K(Y-1/2)>2K>2R+1+bw. Thus the old carrier coordinate is recovered after, rather than assumed before, margin positivity. The old CRT condition is F divides (H_old-C), not F divides H_old. Since F is 1 modulo C and B1<C, its positive quotient is B1+j0C with j0 nonnegative. The reverse parameter is exactly 1+((F-1)/C)B1+Fj0. This validates the positive variable j=j0+1 without an unproved cofinality argument.

The two radicands cannot agree after margin recovery. In particular C>K and A^2>=2P; with F>=A^2, the product DFI is strictly larger than (P^2-1)K^2+1. Hence the rational signed sum of the two roots is nonzero. Isolating each root proves it rational; an integer radicand then makes it integral. The scaled root divided by 2048 (or 8) is separately rational with integer square, hence integral. This order avoids a false inference from a possibly zero rational sum.

### Positive final witness

For completeness, choose positive square roots. The formula

    n=m(V0+V1+r0+r1)-(bw)^2-Q/J

is integral. Since A>bw, D>=A^2 and D>C^2, the subtracted expression is less than 2D, while m>=1 and both supplied V1 choices exceed 2D. Therefore n is strictly positive. This is why the positive-domain equation does not need an extra shift in this coordinate.

### Refined majorant

The inherited proof requires only A>=729, C>=1 and i>=1, all satisfied here. The independent local script verifies its exact remainder and quotient identities. Its finite seventh-order bound and remainder inequalities are valid for these hypotheses. One harmless arithmetic typo in the retained proof is explicitly corrected in the new proof: the negative coefficient magnitudes of t7 sum to 1619, not 1719. Both are below 2048; the positivity conclusion is unchanged. The retained original document is not silently edited.

## Proof boundary

This is a mathematical/literal audit, not a new Lean or Rocq certificate. The unbounded source compiler, its logical calibration with syntactic ZFC refutation, and the inherited numerical ratio theorem remain explicit dependencies. The separate source and carry checks establish finite universal extraction identities, not those unbounded theorems. Together with those retained mathematical dependencies, the composition proves in ZFC that absence of solutions is equivalent to Con(ZFC). Neither the checks nor the equation prove Con(ZFC), global minimality, or a smaller Turing machine.

## Reproduction

From the package root, run:

    python nine_audit/check_local_identities.py
    python nine_audit/independent_nine_audit.py
    python -O nine_audit/independent_nine_audit.py

Python and SymPy are required. The checker reads sibling `nine`, `source`, and `carry` artifacts. It does not need the search binaries, a Git checkout, network access, or the upstream archive executables. Receipts are written only in this audit directory.
