# Exact total degree of the frozen universal Grill polynomial

Date: 2026-10-03

## Result and scope

The integer polynomial computed by the already frozen `universal.dag` has **exact total degree 69,339,973**, with every one of its six external coordinates and 797,135 supplied witness coordinates assigned degree one.

The preceding syntactic upper bound 71,731,007 remains a valid upper bound, but is larger than the true degree by 2,391,034. This follow-up does not change a single source gate, coefficient, witness, comparison, or finalizer. It does not optimize the circuit or claim a minimal degree among different representations. In particular it does not replace the polynomial by one having the same zero set.

The degree theorem itself is an unconditional statement about the pinned arithmetic source. It needs no validity assumptions on histories, residuals, or positive tuples and imports no universality theorem. The universality interpretation of that source retains its separately stated theorem dependencies.

Pinned object:

- `universal.dag`: SHA-256 `a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2`
- `universal.json`: SHA-256 `41e6f754df8f60448e1207ef36e6161729b52004fac719a580d6ec643d039d49`
- `native_unit_kernel.json`: SHA-256 `2d88343037c08fe8b073f67dca531ee73309c0735c1d98a23c20b9ddb1eb08ae`

The source has 3,600,546 binary gates. Gate identifiers below are zero based. Original source and Report 23 are unchanged.

## 1. The cancellation is an identity on every tuple

Use the following abbreviations for actual frozen registers:

| Symbol | Native register | Gate/input |
|---|---|---:|
| u | `and__wn2` | 3,600,220 |
| a | `and__R12` | 3,600,228 |
| c | `and__R10a` | 3,600,226 |
| gamma | `and__ga` | input index 797,137 |
| d | `and__a4m5` = 4a+3 | 3,600,232 |

The first unit factor is gate 3,600,240, `and__R15`:

R15 = (u+ac+gamma d)^2 − (a^2+d)c^2.

In the integer polynomial ring on four independent indeterminates u,a,c,gamma,

R15 = u^2 + 2uac + 2u gamma d + 2ac gamma d + gamma^2 d^2 − dc^2,   d=4a+3.

This follows by expanding the square and canceling the two identical a^2 c^2 terms. The checker also compares the exact sparse coefficient dictionaries of both sides: each has eleven nonzero monomials after expansion. Its symbolic term ceiling is 256; no expansion in the actual 797,141 coordinates is attempted.

Every one of the 67 frozen native-kernel rows is matched exactly to the binary source before the identity is used. Constants, operand identifiers, operation codes, supplied inputs, ports, unit factors, and the unit output match. The identity is therefore a valid way of evaluating the degree of the existing polynomial, independently of any residual equality.

## 2. Leading forms at the outer/native interface

For a nonzero polynomial R, write R_top for its highest homogeneous part. The homogeneous expressions below refer to independent supplied coordinates, not to values satisfying the Diophantine conditions.

Set

- s = 794,976, g = 2,030, N = g+s+5 = 797,011
- K = 2^551890
- p = K (X+Z0) Vfinal (sum of all s supplied native.Shat coordinates)
- alpha = 3N = 2,391,033
- Q = 16 p^N

Here X is the supplied loader witness, not the ordinary external input x. Directly from P=(B−1)J+1, B=KD, D=(X+Z0)Vfinal+X+phase_initial+height_slack, and J=sum(Shat)−s, we obtain

P_top = p,   deg P = 3.

The scale port is P^N, so the native q has highest part Q and degree alpha. All coefficients in p are positive and p is visibly nonzero.

For the joined Z port, the uniquely highest summand is P^(g+s+1) H_V. Indeed the S lane has degree 3(g+s)−2, while the T lane has degree 3(g+s)+4, and the low group pack has smaller degree. Thus

Z_top = p^(N−4) H_V,   deg Z = alpha−11.

The H and M ports both have degree at most alpha−2. These statements also follow directly from the all-row degree pass. They do not require cancellation assumptions.

Write beta for native `and__odd_half`, and put b=2 beta. Let w,f,i,gamma,tau,eta,zeta be the supplied native auxiliaries with corresponding names, and k=eta+zeta. The relevant homogeneous pieces are

u_top = wQ,
(and__sn2)_top = bQ,
c_top = kbQ,
a_top = wbQ^2.

In particular deg u=alpha+1, deg c=alpha+2, and deg a=2alpha+2.

## 3. Exact degree of the first factor

The six terms in the identity in Section 1 have degree bounds, in their displayed order,

2alpha+2, 4alpha+5, 3alpha+4, 5alpha+7, 4alpha+6, 4alpha+6.

The fourth term alone attains the maximum 5alpha+7. Since d_top=4a_top, its leading form is

(R15)_top = 8 gamma a_top^2 c_top
           = 8 gamma w^2 b^3 k Q^5.

This polynomial is nonzero. Therefore

deg R15 = 5alpha+7 = 11,955,172.

Naive max/sum degree propagation assigned 6alpha+8 = 14,346,206 to the original norm subtraction. Its leading a^2c^2 terms cancel identically. Resolving that cancellation lowers this factor's degree by alpha+1 = 2,391,034.

## 4. Other factors and the residual-square finalizer

For the remaining unit factors, the unique or explicitly collected highest pieces give:

(and__R16)_top = a_top^2 f^2 = w^2 b^2 f^2 Q^4,
(and__bs_packed)_top = 16 Q^3 Z_top,
(and__H17)_top = −32 Q^3 Z_top,

(P17)_top = 1024 w^2 b^2 f^2 Q^10 Z_top^2,
(first_unit)_top = 4 w b^2 k Q^3 (tau−k),
(bs_q)_top = Q.

The factor tau−k is a nonzero linear polynomial because tau, eta, and zeta are independent coordinates. Thus none of the four factor leading forms vanishes in the polynomial ring.

Their exact degrees and sum are:

| Factor | Exact degree |
|---|---:|
| R15 | 5alpha+7 = 11,955,172 |
| P17 | 12alpha−16 = 28,692,380 |
| first_unit | 3alpha+5 = 7,173,104 |
| bs_q | alpha = 2,391,033 |
| Their product U | 21alpha−4 = 50,211,689 |

The final polynomial is exactly

F = U (1 + sum of all 86 residual squares) − 1.

The largest residual degree is uniquely attained by residual index 6, the native comparison `ic22=R16`. Since ic22=(i c^2)^2,

(ic22−R16)_top = i^2 c_top^4,

deg(ic22−R16) = 4alpha+10 = 9,564,142.

For completeness, the upper bounds for the first ten, native residuals are

3, 5, 4, 3, 4alpha−11, 4alpha−11, 4alpha+10, 4alpha−11, alpha−2, alpha−2.

The next 75 loader residuals have degree at most 397,489; the final width residual has degree at most two. These bounds are calculated from all source rows, rather than inferred from zero-set semantics. The uniquely highest square is consequently the square of residual 6, with leading form i^4 c_top^8 and degree 8alpha+20 = 19,128,284. The added constant one cannot affect that leading form.

Multiplication of nonzero polynomials adds degrees over the integral domain Z[all supplied coordinates], and subtracting one cannot affect a positive-degree leading form. Therefore

deg F = (21alpha−4)+(8alpha+20) = 29alpha+16 = **69,339,973**.

## 5. Explicit leading form and an exact nonzero ray coefficient

Combining the preceding formulas and substituting b=2 beta and Q=16p^N gives the entire highest homogeneous component:

F_top = 2^138 p^(29N−8) gamma w^5 beta^15 k^10 f^2 i^4 (tau−k) H_V^2.

This displayed polynomial is nonzero. Its degree is

3(29N−8)+40 = 69,339,973.

For an even simpler coefficient certificate, set *every supplied coordinate*, including all six external coordinates, equal to the same indeterminate t. Then p has leading coefficient 2^551891 s, k has leading coefficient 2, and tau−k has leading coefficient −1. Hence the leading coefficient of the univariate specialization is exactly

−2^148 (2^551891 · 794976)^23113311.

This integer is strictly negative and in particular nonzero. It is represented by this exact compact expression; it is never expanded or stored as a giant integer.

Two independently computed residues of that coefficient are:

| Modulus | Leading coefficient residue |
|---|---:|
| 17 | 3 |
| 1,000,000,007 | 53,942,795 |

Nonzero modulo even one integer modulus suffices to prove an integer coefficient is nonzero. No probabilistic identity-testing conclusion or assumption of prime modulus is needed. These are deterministic certificates at the stated explicit specialization, not merely failure-to-detect-cancellation heuristics.

## 6. Streamed certificate, limits, and replay

`check_degree.py` is newly written for this degree result, imports only the Python standard library, and reads the original binary/JSON as data. It does not import or execute the producer, the historical source's Python, the former leading-form checker, or upstream bytecode.

For every gate it propagates a valid total-degree bound and the coefficient at that degree after substituting every supplied coordinate by t, modulo each stated modulus. At additions/subtractions it keeps only operand coefficients at the maximum bound; at multiplication it multiplies coefficients and adds bounds. These rules remain valid when an intermediate leading coefficient is zero: they certify an upper bound and its coefficient, never promote a zero coefficient to an exact degree. The sole special rule is at R15, where the exact, structurally checked identity from Section 1 supplies an improved bound and coefficient. All other gates, including every one of the 86 squares and the complete output, are read from the original frozen stream.

The checker establishes the output bound 69,339,973 and a nonzero coefficient at that same degree. It also checks that the streamed output coefficient agrees with the compact closed-form ray coefficient from Section 5.

Explicit resource limits:

- At most 4,000,000 source nodes and 800,000 supplied coordinates
- At most 256 monomials in the four-indeterminate identity calculation
- 512 MiB address-space ceiling, 180 CPU-second and wall-time ceiling
- Two compact arrays per pass, one degree and one coefficient per source gate
- No full multivariate expansion; no degree-sized univariate coefficient arrays

Replay commands (substitute the extracted Report 23 arithmetic directory for SOURCE_DIR):

python check_degree.py --source-dir SOURCE_DIR
python -O check_degree.py --source-dir SOURCE_DIR --output degree_certificate_optimized.json

`degree_certificate.json` records all source pins, all kernel and port degrees, all 86 residual bounds, factor degrees and leading residues, the exact identity's eleven monomials, and resource usage. `degree_certificate_optimized.json` is the optimized-mode replay. The checker uses explicit runtime failures rather than executable assert statements, so correctness checks remain enabled under Python's `-O` mode.

The Report 23 extraction has these unchanged files under `reproducibility/frozen/arithmetic/`; pass that directory as SOURCE_DIR. The three expected hashes are verified before any arithmetic analysis.

An independently implemented reviewer derives the same full leading form and performs a separate raw-DAG pass; its detailed audit and receipt are stored in `independent-review/`.
