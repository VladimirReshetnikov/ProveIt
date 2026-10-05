# Independent review of rational ordinate reconstruction on all 99 independent values

**PASS, with no correction requested.** The fixed rational reconstruction
of y on the full literal y-independent boundary has finite ordinary-input
projection on every valid fixed complete84 compiler slice. The stated
strict cutoff and the literal-substitution corollary hold with their
explicit nonzero-denominator and integral-ordinate conditions. Setting
H=1 covers every fixed integer-polynomial substitution on all 99 values.
No operation count or witness count changes.

## 1. Actual source boundary

I read all 84 actual source records and their 25 supplied names as inert
data. An independently written dependency-set walk recovers exactly
70 computed plus 23 supplied values independent of both T and y, and
75 computed plus 24 supplied values independent of y alone. The first
list agrees with the frozen E93 receipt; both lists agree with the new
author metadata. The supplied addition is exactly T, and the five
computed additions are

    auxiliary_Tf           = T*f,
    auxiliary_Tf_minus_one = T*f-1,
    auxiliary_c_Tf         = c*(T*f-1),
    aux_u_rhs              = c*T*f-c-R*f^2,
    H2                     = (c*T*f-c-R*f^2)^2.

The existing E93 includes `auxiliary_R_f2=R*f^2`, so no sixth computed
value is missing. The sole direct y consumer is `aux_y2=y_aux*y_aux`.
Every source row and supplied port remains live; the count is the same
84 = 47M + 37A. This is a boundary audit, not a new source construction.

The actual rows for `c2`, `Ac2`, `aux_coefficient_root`, `R16`, the auxiliary
factor, the scaled strong factor and the final product bind the author's
abbreviations S=Delta*i*c^2, Q=S^2, V=cTf-c-Rf^2 and
F84=P5*Na*Ns_scaled-Delta. The five factors in P5 are the retained first,
main, input, index and transport factors. No algebraic evaluation of a
saved array was used in this audit.

## 2. Growth and coefficient estimates

The complete prior ordinate proof and independent review supply, on
full positive parent zeros, Na=1, Ns_scaled=Delta, the exact native input
bound u=2*d_native*x+b_source<R, R<c<f, Delta<c<f, f>=2, Q<f^3, and
all 93 old argument bounds |E_j|<=f^3. Their domains are exactly the
unchanged positive source domain on a valid compiler slice. They do
not choose a special auxiliary completion.

The signed-quotient theorem's growth section applies in particular to
these positive tuples. It gives |V|>f^(R-1) and
|V|<f^2|T|+f^3. Since the actual index has R>=5, assuming
T<=f^(R-4) would give |V|<2f^(R-2)<=f^(R-1), a contradiction. Hence
T>f^(R-4). The strictness and the exponent shift by four are correct.

After fixing E93 at one parent zero, put a0=cf and b0=c+Rf^2. These are
positive integers satisfying a0<f^2 and b0<f^3: the latter follows
explicitly from c,R<=f-1. Thus the coefficient norm of
v(z)=a0*z-b0 is less than 2f^3, and that of v(z)^2 is less than 4f^6.
The old constant arguments, z, zf, zf-1 and c(zf-1) all meet the common
4f^6 bound as well. No equation is asserted to remain true while z
varies; this specialization only constructs proof polynomials.

For fixed formal integer polynomials P,H with total degrees at most t,
submultiplicativity of the coefficient norm gives

    ||p||_1 <= Lp*4^t*f^(6t),
    ||h||_1 <= Lh*4^t*f^(6t).

Formal dependencies and cancellations may reduce these quantities and
cannot enlarge them. The assumption H(actual)!=0 gives h(T)!=0, which
ensures that the specialized h is nonzero even after a degree drop.

## 3. Nonvanishing after every specialization and the cutoff

The actual ordinate equation gives a root T of the integer polynomial

    J(z)=(Q-1)*p(z)^2-[Q*v(z)^2-1]*h(z)^2.

Q=S^2 with S>1 and a0>0, so Q*v(z)^2-1 has the two distinct rational
roots (Sb0+1)/(Sa0) and (Sb0-1)/(Sa0), each simple. If p is nonzero,
identity J=0 would equate an even vanishing order on the left with an
odd order on the right at either root. This remains a contradiction if
p or h vanishes at that root. If p is identically zero, the nonzero
quadratic times the nonzero h^2 cannot vanish identically. This proves
J!=0 after every allowed specialization, not just generically.

The norm estimates correctly yield

    ||Q*v^2-1||_1 <4f^9+1<=5f^9,
    ||J||_1 <=4^(2t)*(Lp^2+5Lh^2)*f^(12t+9).

The p-term originally has the smaller f-exponent 12t+3; weakening it to
12t+9 is legitimate. J has integer coefficients and hence a nonzero
leading coefficient of absolute value at least one. The elementary
Cauchy bound gives T<=1+||J||_1<=K*f^(12t+9), with precisely the author's
K=4^(2t)*(Lp^2+5Lh^2)+1. A nonzero constant J cannot have the required
root, so a complete degree drop causes no exception.

If R>=12t+13+ceil(log2 K), then f>=2 gives
f^(R-4)>=K*f^(12t+9)>=T, contrary to the strict growth estimate. Thus

    u<R<12t+13+ceil(log2 K).

The bound depends only on the fixed formulas and compiler slice. A
fixed finite family therefore still has finite input projection. The
proof handles P=0 and formally or specially low-degree polynomials;
H(actual)!=0 excludes the zero denominator case throughout.

## 4. Signs, zero ordinate and retained limits

For a literal rational substitution, a nonzero integral quotient g can
be replaced by |g|. The sole square consumer preserves the complete
output, and every E99 argument remains fixed. This restores a full
positive parent zero before any native theorem is applied. The squared
root relation also covers an ordinate equal to |P/H| directly.

For g=0, the displayed all-ring factorization is the already reviewed
source identity

    F84|y=0 = Delta*(Delta^2*i^2*c^4*V^2*P5
                    *(f^2-Delta*i^2*c^4)-1).

The other positive ports give integer Delta>=8 before any equation.
The product inside the bracket is divisible by Delta^2 and cannot be
one. This excludes the zero-ordinate sector without applying parent
soundness outside its positive domain. Integrality of g is essential
to sign restoration; H=1 makes it automatic for polynomial substitution.
Denominator-cleared zeros at poles are outside the theorem.

The separate rational reconstruction of f really uses T,y,y^2 and
therefore does not contradict the current simple-root argument. The
scout's identity and the subsequent complete90 theorem's statement
support the author's retained warning against extending this result
to every witness. The older rational E88 argument already appears in
Section 7 of the full-independent-root note, as the author acknowledges.

No wrong or unproved new claim arose in this review. No source lowering,
arithmetic optimality, altered auxiliary equation or joint-coordinate
elimination is inferred. The author's two remarks and open question
retain those scope boundaries explicitly.

## 5. Evidence and read scope

The companion reviewer receipt binds the frozen author note and metadata,
authenticates all six author proof dependencies and their declared read
spans, and binds the actual84 source. It embeds the independent static
source census and five-row comparison. The temporary scratch metadata
is not an additional frozen artifact.

I read the complete new note and receipt, the complete prior ordinate
note and its independent review, signed-quotient lines 1--47 and 190--226,
the prior rational E88 argument at lines 171--199, the complete rational
root scout, and the complete90 theorem/source-introduction lines 1--48.
The actual84 arrays and the old E93 census were inspected only as
structural metadata. Older native/compiler proofs are inherited through
the stated reviewed interfaces; authentication does not enlarge this
read scope.

Only original inline byte, span, name-dependency, row, count and liveness
metadata ran. No supplied, archived, committed, predecessor or frozen
scientific helper was executed or imported. No saved source was
numerically or symbolically evaluated, no degree was propagated, and
no large native witness was constructed. The conclusion follows from
the all-size proof above, not finite arithmetic experiments.
