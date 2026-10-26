# Round22: natural triangular syntax charts

## 1. Result and logical scope

The new raw chart has **202 independently nonnegative integer variables,
154 quadratic residuals, 9,652 expanded monomials, and coefficient height
13,654,244**. Its polynomial is the sum of the squares of precisely the
residuals in `chart202/equation.json`. Every collected coefficient is in
`chart202/expanded_polynomial.json`. The exact degree is four.

The selected primary profile has **202 variables, 154 quadratic rows,
9,353 terms and height 1,854,167**. Its low-height companion has **16,927
terms and height 416,488**. The 203- and 204-variable selected profiles have
respectively **6,524 terms / height 1,979,888** and **6,503 terms / height
1,981,520**.

The selected reversible row-basis profiles do not change the
variable count, row count, solution set, or proof: their only additional
operation is `R_i <- R_i + k R_j`, with integral k and i different from j.
The `SUMMARY.json` and per-profile coefficient files give their exact metrics.
No global optimality is claimed.

This is a domain-preserving change to the round21 natural construction, not
an integer-domain relaxation. The inherited proof and complete construction
are preserved under `inherited/`, including its parent proofs and calibrated
logical source. Its theorem is that a natural zero exists if and only if the
fixed effectively presented ZFC calculus in its C222/ZF/ZFC calibration has a
finite syntactic refutation. Composition with the exact natural bijection
proved below gives the same theorem for the new quartic. In particular ZFC
proves that its no-natural-zero sentence is equivalent to `Con(ZFC)` in that
specified calibration. This neither assumes consistency nor claims a new
end-to-end kernel formalization of the displayed coefficients. The Python
checks establish finite exact algebra and the finite nonnegativity criteria;
the inherited Pell and syntactic arguments remain ordinary mathematical
proofs.

## 2. The triangular gate-chart lemma

Let R be an integral residual system in variables x, all ranging independently
over N={0,1,...}. Let S be a subset of its gate coordinates. Suppose these
gates admit an order g_1,...,g_s and retained defining rows

    x_(g_i) - f_i(x)=0,

where f_i has nonnegative integer coefficients, does not contain x_(g_i),
and every coordinate from S occurring in f_i belongs to g_1,...,g_(i-1).
Coordinates outside S need not be gates and require no new interpretation.

Perform a finite sequence of elementary coordinate changes

    new x_v = current x_v + L(current x),                 (1)

where v belongs to S and L is an affine polynomial with nonnegative integer
coefficients, not containing x_v. Every step is an integral affine
bijection on Z^n, with inverse substitution

    current x_v = new x_v - L(new x).                     (2)

Let F be the composite forward map, G its integral affine inverse, and let
the new rows be R_j(G(y)). Then F and G restrict to mutually inverse
bijections between the NATURAL zero sets of the two systems.

Proof. If x is a natural zero, each elementary forward step (1) remains
natural; affine substitution gives the new rows zero. Conversely let y be
a natural zero of the new rows and put x=G(y) in Z^n. Every coordinate
outside S is unchanged and hence nonnegative. Exact substitution gives all
original rows R_j(x)=0. Induction along the specified gate order gives
x_(g_i)=f_i(x)>=0, since all coordinates occurring in f_i have already been
shown nonnegative. Thus x is entirely natural. The formal identities
G(F(x))=x and F(G(y))=y give the bijection. QED.

The inverse (2) is NOT asserted to preserve the whole orthant. For example
new x_v=0 and L=3 would give x_v=-3 at an arbitrary point. Naturalness is
proved only on the residual zero set, from the retained defining rows.
This distinction is essential. No semantic outer coordinate, denominator,
Pell ordinate, orientation, source remainder, or proof-code coordinate is
translated in the present application.

All substitutions are affine, so every transformed residual is still
quadratic. Hence its sum of squares has degree at most four. The supplied
coefficient lists exhibit nonzero fourth-degree terms, proving exact degree
four.

## 3. The twelve literal elementary changes

Use the inherited variable labels as formal coordinate names. They label
NEW chart coordinates after a change; they should not be read as claiming
unchanged numerical values. `variables.tsv` preserves those names for
cross-referencing, and `chart_certificate.json` gives the exact forward and
inverse maps. Set a=`crt.encoded.a`, b=`crt.encoded.b`, and
G=`syntax.shared_shifted_square`. In the following sequential list, every
right-hand side means its CURRENT value at that step:

1. `mul.36 += 2b+3`.
2. `mul.97 += 8b+mul.36+4mul.60+11`.
3. `mul.173 += 2a+mul.74+16G+16`.
4. `mul.243 += 16mul.232+4mul.237+33`.
5. `mul.131 += 2a+4mul.36+mul.74`.
6. `mul.48 += 32mul.36+4G+34`.
7. `mul.225 += 16mul.214+4mul.219+34`.
8. `mul.274 += 16mul.263+4mul.268+34`.
9. `mul.148 += 16mul.36+4G+18`.
10. `mul.317 += 5mul.36`.
11. `mul.256 += 2add.253+2`.
12. `add.253 += a`.

The last change really occurs after the preceding one; collapsing the list
without respecting that order would give an incorrect forward map. The
machine-readable authoritative list is `shears.json`.

For the 202-coordinate parent, the gate-defining rows in restoration order
are the following (all row numbers are zero-based in
`inherited/pooled202/equation.json`):

| gate | defining row |
|---|---:|
| mul.36 | 6 |
| mul.48 | 8 |
| mul.97 | 14 |
| mul.131 | 18 |
| mul.148 | 20 |
| mul.173 | 23 |
| mul.225 | 30 |
| mul.243 | 33 |
| add.253 | 35 |
| mul.256 | 36 |
| mul.274 | 39 |
| mul.317 | 45 |

Each is literally a monic output minus a coefficientwise nonnegative
polynomial. Any translated gate on its right has an earlier defining row.
The independent checker verifies these facts from the literal parent rows,
not from comments or a presumed interpretation of gate names.

The 203- and 204-coordinate companions apply exactly the same named changes
when their target survives that parent's contraction. The absent targets
are respectively `{mul.173,mul.131}` and
`{mul.97,mul.173,mul.131}`. Every referenced input of a retained change still
exists. Their own defining-row orders and nonnegative polynomial criteria
are independently checked. This yields 203/155 and 204/156 quartics with
6,937 and 6,982 terms respectively before residual row-basis changes, both
of height 13,654,244.

## 4. Why the new chart is simpler

These changes select useful affine accumulators instead of retaining only
multiplication outputs. For a concrete exact identity, let m be the old
`mul.36`, g the unchanged shifted-square coordinate, and p the old `mul.48`.
The old `mul.55` defining polynomial is

    (2p+128b+64m+8g+259)(2p+128b+64m+8g+260).

After step 1 let l=m+2b+3. Step 6 gives

    z=p+32l+4g+34 = p+64b+32m+4g+130.

The entire dense polynomial consequently becomes

    (2z-1)(2z)=4z^2-2z.

This removes many cross terms and large constants from one residual with
no new variable and no divisibility condition. The new z is natural for
every old natural solution. Although 4z^2-2z has a negative displayed
linear coefficient, no new nonnegativity axiom is inferred from that
expression: the gate-chart lemma restores the ORIGINAL nonnegative
polynomial equations before invoking any parent theorem. Other listed
changes perform analogous cancellations.

The coefficient-height reduction is not just multiplication of the whole
polynomial by a constant or cancellation of a common gcd. The quartic is
re-expanded exactly after the coordinate changes, and all coefficients are
supplied as literal integers.

## 5. Residual-basis refinements

For any integral k and i != j, the transformation

    (R_i,R_j) -> (R_i+k R_j,R_j)

is invertible by subtracting k R_j. Thus it preserves the common residual
zero set over any integral domain. On natural inputs, a sum of integer
squares is zero exactly when each residual is zero. Applying the supplied
sequence of row shears and then re-squaring therefore preserves the natural
zero set. This is not an assertion that the numerical sum-of-squares
polynomial is unchanged. Each selected profile has its own literal expanded
coefficient list and exact forward/reverse certificate.

## 6. A separate 200-variable degree-eight tradeoff

This secondary companion does not improve quartic dimension. In the raw
202-coordinate chart eliminate only U=`pooled_power.U` and
K=`pooled_power.K`, retaining M=`pooled_power.M`. Let n be the authenticated
q=`pow2.output`, A=`shared.lower_A`+`shared.A_slack`, and
T=2An-n^2-1. Retain the same three Pell pairs (Y_i,Z_i) and the same affine
output expressions m_i from the inherited pooled-q proof. Replace its three
quadratic rows

    R0=U-sum Y_i^2,
    R1=K-2sum Y_i(m_i+Z_i)-(2A-n)M+nU,
    R2=sum(m_i+Z_i)^2+M-nK

by the single quartic residual

    Q=sum(m_i+Z_i-nY_i)^2-TM.

The literal identity is Q=R2+n R1-n^2 R0. No other residual uses U or K.
The resulting sum of squares has 200 variables, 152 residuals, exact degree
8, 10,392 terms and coefficient height 13,654,244.

A 202-coordinate natural zero clearly projects to a 200-coordinate zero.
Conversely first restore the syntax chart by Section 2, which uses none of
these three pooled rows. The retained authentication order in inherited
PROOF.md, Section 4.1, still recovers n=q>0 from the unchanged unpooled
power graph before interpreting the pooled powers. Define

    U=sum Y_i^2,
    K=2sum Y_i(m_i+Z_i)+(2A-n)M-nU.

U is natural and K is an integer by this polynomial formula. The equation
Q=0 gives

    nK=sum(m_i+Z_i)^2+M>=0.

Since n>0, K>=0. This restores all three quadratic pooled rows with natural
witnesses and hence a natural zero of the 202-variable quartic. Integrality
of K does NOT rely on unproved divisibility of a displayed quotient. Thus
the octic has exactly the same refutation/no-zero calibration.

## 7. Authentication and verification boundary

No round21 Pell, factorial, CRT, local-source, or index-cap row is deleted
by the quartic chart. The previous strengthened lower frame, exact additive
frame budget, and inverse-power treatment of the y+1 seed are inherited
unchanged. In particular this round does not reinstate a discarded
predecessor orientation, nor use a semantic positivity claim before its
parent proof establishes it. Gate restoration recovers the literal parent
system first.

`check.py` is independent of the builder. It uses sparse exponent maps,
checks both composite affine identities, reconstructs every transformed
row from the explicit inverse map, checks the original gate polynomials
and dependency order, and independently convolves every sum of squares.
It also verifies the octic elimination and natural-K identity. Both normal
and `python -O` executions must pass; no correctness check uses `assert`.
`verify.py` reruns the builder in a fresh temporary directory and compares
all generated coefficient and certificate files. `render_equation.py`
round-trips every printed TeX residual to the exact coefficient list.
These finite checks do not by themselves prove the unbounded calibrated
ZFC equivalence; that theorem is the ordinary proof here composed with the
fully retained inherited proof chain.
