# Independent internal review of the 42-integer quartic

This review was conducted by a separate research agent within the same
AI-assisted session. It is not external human peer review or a kernel
certificate. The review reads `PROOF.md`, the literal 42-variable packet,
the source 45-variable proof, and the inherited ordinary strong-rank proof.

## Mathematical assessment

No gap was found in the new common-sign recovery argument. Its ordering is
essential and is respected: the proof obtains the main Pell rank before
invoking the old whole-system soundness theorem that requires the missing
individual positivity guards.

The following points were checked independently.

1. The new product guard gives a common sign, not positive signs. With
   `sigma=sign(k)`, `kappa=|k|`, `t=|Y|`, and `theta=eta/k`, one has
   `0<theta<1`. For positive Y, `|c|/kappa=t+theta`; for negative Y,
   `|c|/kappa=t-theta`. Since `t>=q^3>2`, both ratios exceed one.
2. The zero-square-scale exclusion does not presuppose the signs of eta
   or zeta. When X=0, the main norm is divisible by `H=4Y+3`, whereas it
   equals 1; `|Y|>=q^3` excludes `H=+1` and `H=-1`.
3. The replacement `w=4u^2` ensures `e=|XY|>4R+8`. The first Pell
   congruence gives `sigma*2n=R+1 modulo e`. Even for sigma negative,
   its least positive representative forces `2n>=e-R-1>R+1`. Thus
   the large-rank bootstrap does not assume the desired common sign.
4. Replacing the signed main parameter by `A=|a+2|` is legitimate:
   its discriminant remains `Delta=A^2-1`. The signed coordinates are
   replaced by absolute values only inside ordinary Pell classification;
   the original exposed congruences are retained with their possible signs.
5. The ordinary strong-rank lemma applies with `c0=|c|` and
   `|2r+1|`, since `c0>A*Delta^2`. Its consequences `c0|m` and
   `m>2p` are sufficient for the signed step-down argument. The
   congruences from `V=fo-c=jc-R` yield `p=+R or -R modulo c0`;
   `0<p,R<c0/2` then yields p=R without a sign assumption on c.
6. For a negative common sign, `e` divides `2n+R+1`, but
   `0<2n+R+1<3R+1<e`, because `n<p=R`. This is a contradiction.
7. Canonical completeness supplies q and w as dyadic powers. The oddness
   of both R and the exponent t in `q=2^t`, together with `R>3q`,
   makes `R-t` even and at least two. Hence replacing the old square
   root by `u=2^((R-t-2)/2)` is valid. This is an existence argument,
   not a reversible map on every predecessor tuple.

After the common sign has been proved positive, supplying ternary
representations for eta and zeta and setting `u_old=2u` gives exactly a
zero of the authenticated predecessor. The source's negative-Y exclusion
and remaining compiler reasoning are inherited dependencies, not newly
proved by this review.

## Independent finite algebra audit

`independent_algebra.py` uses its own AST parser and sparse integer
polynomial arithmetic, without importing the main builder. It independently
checks the 25 unchanged residuals, both modifications, all used input
names, 42 unknowns, 27 quadratic residuals, 391 terms when fixed ports
are symbolic, and exact degree four through the coefficient 1 of tau^4.
Both normal Python and optimized Python executions pass. The resulting
receipt is `INDEPENDENT_ALGEBRA.json`.

These finite checks verify the displayed algebra. They do not establish
the inherited unbounded compiler theorem, object-language ZFC derivability,
or the existence or absence of any integer zero.

## Fixed-instance and inherited-chain replay

The complete active source-34 tuple has now been authenticated, rather
than left as four formal coefficient ports. `verify_dependencies.py`
checks 73 exact source files against their Git blob identities and
SHA256 digests, regenerates all 532,479 raw coefficient bytes, and runs
the independent actual-coefficient decoder. It also checks the exact
recorded Q54/Q51/Q50/Q45 parent hashes, all 30 odd-scale substitutions,
the packing-register identity, 28 unchanged Q50 rows, 25 unchanged
Q45 rows and the three Q45 guard formulas. The recorded replay passes.

The literal transport residual was independently checked against the
historical Q45 prose. Its coordinate is already shifted and its required
restored guard is `z>0`; the old product coordinate would be `z+1`.
The corrected proof in `PROOF.md` and dependency README explicitly uses
the literal equation. This correction does not alter any residual or
the new common-sign argument.

The included dependency map distinguishes the ordinary mathematical
compiler/calibration interface from a fresh formal-assistant build.
The archive contains the literal K215 table and its ordinary calibration
exposition, plus the precise Lean endpoint statement. It does not contain
the whole transitive Lean/Rocq runtime development and does not claim to
rebuild that inherited endpoint offline.
