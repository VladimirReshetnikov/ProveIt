# Independent review of the admissible-denominator Pell construction

## Decision and scope

**Accepted at the stated ordinary-proof boundary.** The four fixed DAGs in
`pell_work/` correctly implement the displayed equations. The new argument
permits either carrier denominator `D=XY` or `D=q^4`, and the unshifted
definition `b=cT-R` is sound for both transport weights `V^2` and `bV`.

This review independently checks the new arithmetic and its use of the
retained Pell interfaces. It does not claim a new Lean/Rocq proof term or
reverification of the complete native compiler and logical calibration.
The consistency conclusion composes with the explicitly retained whole
indexed BFS943 coefficient tuple and its ordinary native/refutation theorem.
The reviewer is a separately tasked AI agent within the same research
workflow, not an outside human referee.

The reviewed files are `PROOF.md`, all four `equation_*.json` files,
`proof_sources/denominator_parent.md`, both `unshift_*.md` notes,
`product_square.md`, `uniform_ratio.md`, `scaled_native.md`, and the
normalized rank, auxiliary-index, parity and reconstruction arguments in
`universal_pell.tex`.

## 1. Extraction of the roots and the integral carrier

Positive input coordinates give `M>0`, `G>0`, `Q>1`, and `|V|>1` before
any assumption about the signs of `B`, `C`, `R`, or `b`. The crucial exact
identity is `Q=4 Delta^2 U^2 G`. Thus every prime divisor of `G` is a unit
in each of `Q-1` and `QV^2-1`. From

    (Q-1)(Z/M)^2 = G(QV^2-1)

its valuation in `G` must be even. This applies to rational squares and
does not require a coprimality hypothesis on `M`. The positive coprime
factors `E` and `F0=1+Delta U^2 E` are consequently squares separately.

The rational adjacent-Pell argument is valid. If `y=r/m>0` is reduced,
clearing denominators gives `m^2 | Q-1`. The descent

    v'=(2Q-1)v-2(Q-1)y,
    y'=(2Q-1)y-2Qv

has integer first coordinate. Since `2Q-1=1 mod m`, the reduced denominator
of the second coordinate remains `m`. For `v=|V|>1`, the norm gives
`v<y<Qv/(Q-1)`, hence `-v<v'<v`. Its first coordinate cannot vanish.
Reflecting signs permits induction on `|v|`; at `v=1` the norm gives
`y=1`. Therefore `y` and `z=Z/M=+/-gy` are integers.

## 2. Main-index folding is uniform at the new base

The construction removes the old artificial scale entirely. It is
essential that the folding interface hold for every integer `A>=3`.
The following direct proof confirms that it does.

The strong norm gives `f=chi_A(m)`, `I=psi_A(m)` for some positive index
`m`. Set `S=Delta I`; then the adjacent norm gives
`S|V|=chi_S(j)`, `y=psi_S(j)`. The index `j` is odd: at even indices the
trace is `+/-1 mod S`, while the actual trace is divisible by `S>=2`.
The odd-quotient recurrence, evaluated at
`S^2=Delta(f^2-1)=1-A^2 mod f`, yields

    psi_A(j) = +/-c mod f.

The addition laws give

    psi_A(j+2m) = -psi_A(j) mod f,
    psi_A(2m-j) = psi_A(j) mod f.

Reduce and reflect to an index `p` in `[0,m]` with the parity of `j`.
Then `c=+/-psi_A(p) mod f`. Since
`0<c<=I`, `0<=psi_A(p)<=I`, and `2I<f` for `A>=3`, congruence forces
the equality `c=psi_A(p)`. Thus `p>=1` is odd. Neither the sign of `V`
nor the parity of the strong index `m` is restricted.

This proof has now been added to section 3 of the released `PROOF.md`,
together with the odd-quotient recurrence. The source ledger was corrected:
the copied `universal_pell.tex` supplies the later normalized rank and
auxiliary-index arguments, while the new proof prints this folding argument
in full. The initial review therefore led to a completed documentation fix.

The first norm gives `k=2psi_(2XY^2+1)(n0)`. If `n0=1`, then `k=2`
and `c=2Y+1`, strictly between the first and second positive ordinates
at base `A=Y(X+1)+1`. Hence `n0>=2`, `k>=8XY^2+4`, and
`c>kY>=k>8q^7`. This proves `Kpos>0` before any transport sign.

## 3. Removing the T shift: both weights are justified

The case `b=0` is impossible: the auxiliary norm would give

    y^2-c^2=(c^2-1)/(Q-1) in (0,1),

whereas the left side is integral. With `D0=Delta U^2>=243`,
`a^2/g^2=D0*a/(1+a)>D0/2>9`. Consequently
`sign(V)=sign(b)`, `|V|>3g`, `|V|>|b|`, and `y<3|V|/2`.
These prove `gy<V^2/2` without assuming `b>0`.

The `bV` weight needs additional work. Its proof cannot borrow the old
shifted inequality `b>c`, because that inequality fails at `T=1` after
unshifting. The new proof correctly excludes the main index three first.
If `p=3`, then `c=4A^2-1`. For `n0>=3`, the elementary bounds

    c<64X^2Y^2<32X^2Y^5<kY<c

contradict each other. Thus `n0=2`, `k=8XY^2+4`. Setting
`u=X+2-2Y`, exact expansion gives

    eta=4Y^2(Xu+1)+8Y(X+1)+3-4Y.

For `u<=-1` the right side is negative; for `u>=2` it exceeds `k`.
Thus `0<eta<k` forces `2Y-X` to be one or two. This contradicts
`q|X`, `q|Y`, and `q>=32`. Therefore `p>=5` and
`c>c3=4Delta+3` before the transport step.

The adjacent index three is then impossible with either sign of `V`:
its two cases would give

    f^2(b-4Delta)=c-c3, or f^2(b+4Delta)=c+c3.

Both right sides lie strictly between zero and `f^2`. Hence the adjacent
index is at least five, `|V|>8Q^2`, and `|b|>4g`. This proves
`L=bV=|b||V|>0` and `gy<3L/8`.

For either weight, `e=b-cT+k-1<b`. The carrier identity

    z=n+kappa-(1+hL)B/h-e/D

therefore yields, if `B<=-1`,

    n<L/2-L+|b|/D<0.

Here `D>=q^4>2`. This is incompatible with the actual positive input
`n`; thus `B>=0` and `C>0`. It is legitimate only now to use the outer
mask bound `3q<R<q^4-2`. It restores `b>0` and `V>0` because `c>2R`.
No inverse positive-coordinate map `T_old=T-alpha` is asserted or needed.

## 4. The denominator recovery has the correct order

The normalized rank and signed auxiliary-index lemmas give `p=R` from
`c^2|I`, the two residues of `V`, and `c>2p,2R`. They require neither
`b>c` nor a previously integral `e/D`.

Now let `D` be any polynomial that satisfies, pointwise on positive inputs,

    D>0, q^4|D, D|4XY^2.

The integer carrier implies `D|hHe`. Since `h=q-1` and
`H=4Y(X+1)-1=-1 mod q`, it follows that `q^4|e`. This cancellation is
valid without assuming that `D` itself is coprime to `hH`, and it does not
need the later parity conclusion.

The first-norm recurrence gives `k=2n0 mod 4XY^2`, so
`q^4|(2n0-R-1)`. Its integer representative is small: since
`2XY^2+1>A`, the case `n0>=R` would force `k/2>=c>k`.
Thus `1<=n0<R` and `|2n0-R-1|<R<q^4`. Consequently

    2n0=R+1.

Only after this equality do we use the complete recurrence modulus to
obtain `4XY^2|e`, hence `D|e`. This proves the full quotient integral.
Both choices in the release satisfy the required condition:
`XY=q^4 ws`, `(4XY^2)/(XY)=4Y`, and
`(4XY^2)/q^4=4wq^3s^2`.

## 5. Projection and completeness

The supplied ratio proof is explicitly valid for every real `lambda>=1`.
Its lower and upper estimates therefore apply at `lambda=1` without a
limiting argument. With `R=2r+1`, `r>=48`, they give
`Y>X^r/3` and `X^(r+1)<3Y(X+1)<H`.

After `rho=e/D` is integral, the carrier gives `H|hKpos`. The projection
cancels only the unit two through odd `H`, and bounds the **entire** product
`h(X-2^R)(2^R X+1)` below `H`. This yields `X=2^R` without cancelling
a possibly nonunit factor. The universal projection then gives integer
`kappa`; the remaining carrier and `W=1 mod h` give `h|B` and `t>=0`.
The built-in `q^3|Y`, fixed-minus parity and half-binomial arguments license
the retained fresh reconstruction at the different source base
`Y(X+1)+2`. The two bases must not be identified.

For completeness, the inherited canonical outer data define the new
first/main Pell pairs at `lambda=1`; the same uniform ratio bound gives
`eta,zeta>0`. The index excess is a positive multiple of `4XY^2`, so its
quotient by each advertised `D` is a nonnegative integer. A positive Pell
matrix period modulo `c^2 tau` supplies a seed ordinate divisible by that
modulus. Doubling produces exactly the new polynomial strong pair.
The generic positive auxiliary construction gives `T>0` directly, with no
subtraction of `alpha`. Finally

    n=gy+(1+hL)t+rho-kappa>0

because `g>kappa`, as follows from `f0>(A-1)I0>Xc>kappa`.
These are fresh canonical witnesses; no pointwise inverse shear is used.

## 6. Independent finite audit

`check_pell_independent.py` separately parsed all four DAGs, checked
topology and complete liveness, and propagated their sparse leading
homogeneous polynomials with the four fixed ports kept as formal
degree-zero symbols. Its expected leading forms were derived directly
from the mathematical definitions rather than copied from a source gate.
All passed:

| Denominator | Weight | Live binary gates | Exact degree | Leading monomials |
|---|---|---:|---:|---:|
| `XY` | `V^2` | 75 | 626 | 390 |
| `XY` | `bV` | 76 | 464 | 47 |
| `q^4` | `V^2` | 76 | 622 | 390 |
| `q^4` | `bV` | 77 | 460 | 47 |

The final one-gate saving uses the already computed `kY`:
`ell=(XY)(kY)` and `E=1+ell(ell+k)`. This equals
`1+XY^2(XY^2+1)k^2` identically. The independent leading-part and scalar
checks were rerun against the updated exact DAG bytes.

The complete leading forms, with `q0=beta J`, `k0=eta+zeta`, are

    2^14 q0^378 w^48 s^110 i^20 k0^64 T^4(q0-F-alpha)^2,
    -2^10 q0^284 w^36 s^82 i^14 k0^46 T^2,
    2^14 q0^378 w^46 s^108 i^20 k0^64 T^4(q0-F-alpha)^2,
    -2^10 q0^284 w^34 s^80 i^14 k0^46 T^2,

in table order. Since the actual `beta>0`, these are nonzero and establish
the claimed exact global degrees. In addition, 120 signed modular points
per DAG agreed with a separate direct scalar implementation. Those 480
checks are regression evidence only; they are not a proof of polynomial
identity, of the unbounded Pell lemmas, or of consistency.

The receipt records SHA-256 identities of the four exact DAGs reviewed.
The source agent's separate verifier supplies the complete exact
free-polynomial cut checks and reconstruction of the fixed coefficient
tuple; this review does not replace that verifier with random testing.

