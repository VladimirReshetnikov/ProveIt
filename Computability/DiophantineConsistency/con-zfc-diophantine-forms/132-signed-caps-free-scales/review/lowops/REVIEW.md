# Independent review: product-main-guard low-operation addendum

## Verdict

**ACCEPT**, as an ordinary two-way arithmetic reduction relative to the explicitly retained native/compiler/finite-refutation calibration. No new proof of consistency or proof-assistant endpoint is asserted. The two literal equations have eleven unrestricted integer variables and exact (degree, live-operation) pairs **(924,109)** and **(840,110)**. They strictly improve the incoming (966,111) and (882,112) tradeoffs. This is a separate addendum; the frozen degree352 family and its review are unchanged.

Reviewed proof SHA256: `a828b2d62f7e2862efc78d0303fb295475dbc301829b16f0bba620744ab7bd9f`.

Literal DAG SHA256 values:

- `product_main_guard11_native.json`: `3b90018065bc96195b240332ecce281227426089224388fdea0a5c5ef6f73ffd`.
- `product_main_guard11_short.json`: `404d1684eba1ced01864a6d6096909dd0818e2f1def520f4848a865d2dd027ff`.

## 1. What changed and why it is valid

Write `Dm=1+Delta*c^2`, `P=Dt*Dg`, `BP=Dm*P`, and `U=A*r*c^2`. The new strong radicand and quotient are

    Df=1+Delta*U^2*BP, Q=Delta^2*U^2*BP, delta=Q-1,
    V=Df(c-R+4U*BP*T)-c, Cy=QV^2-1, Da=delta*Cy.

With `S=srH`, `Z=Sn-Ac`, the equation is

    delta*Z^2-S^2*BP*Df*Cy=0.

This replaces the incoming strong multiplier `A*r*c^2*Dm` by saturation with the square root of `Dm*P`. The reduction cannot assume `Dm` is already a square: its early folding argument below is essential.

### Soundness bootstrap, including all signs and c=0

The original cubic ordinate `Y=(2v+1)q^3` gives `|A|>=3`, `Delta>1`, `H!=0`, and `Dm>0` before any root extraction. The consecutive-product first radicand `Dt` is positive; `Dg` is odd, so `P` and `BP` are nonzero without claiming either positive. The integer-size arguments make `Df`, `delta`, and `Cy` nonzero even when `BP<0`. The zero-free homogeneous intersective quintic makes `Ac!=0`; specializing the final equation at `S=0` gives `delta Ac^2!=0`. Thus `r,s` are nonzero at a zero.

All three factors `BP,Df,Da` are pairwise coprime as absolute integers, without a positivity assumption. Modulo `BP`, both `Df` and `Da` are1. Modulo `Df`,

    Q=-Delta, delta=-A^2, V=-c, Cy=-Dm, Da=A^2*Dm.

Since `A|U` and `Dm|BP`, `Df` is1 modulo both `A` and `Dm`. Multiplying the equation by `delta` gives `(delta Z/S)^2=BP*Df*Da`, a nonzero integer square. Pairwise coprimality therefore makes the absolute value of every factor square.

The sign extraction is correct: `Delta*A^2` is divisible by4 for every integer `A`, so `Df=1 mod4`, even for negative `BP`. A negative square is never1 modulo4, hence `Df>0`. If `c!=0`, then `U!=0`, and negative `BP` would make `Df<0`. If `c=0`, then `U=0`, `Dm=Df=Da=1`, so the product identity itself makes `BP=P` positive. Thus `BP,P,Da` are positive in every case. Write `p0^2=BP`, `f^2=Df`, `e^2=Da`.

It now follows that `Dg>0` and `Budget>=2`. The centered strip and common-sign disk estimates are licensed at this point, not before it. They exclude `c=0` and give the original strict packing bounds.

### Early folding removes the potentially circular main root

Set `I=U*p0` and `T_old=p0*T`. The strong and auxiliary identities become exactly the retained ones, with `c^2|I`, `|I|>=c^2>=|c|`, and `I!=0`. The adjacent-Pell denominator descent makes `y=e/delta` integral; it is not inferred merely from `Da` being square.

The absolute folding lemma needs only the strong and auxiliary norms and `|c|<=|I|`, not the first-Pell square. With `B=|A|>=3`, `I0=|I|`, and `C0=|c|`, classify the strong pair as `f=chi_B(m)`, `I0=psi_B(m)`. Then `f>2I0`. The auxiliary index is odd; its quotient-polynomial identity gives `psi_B(nu)=+/-C0 mod f`. Folding to `0<=p<=m` and using `psi_B(p)+C0<=2I0<f` forces `psi_B(p)=C0`. This proves `Dm=d^2` independently of `Dt` or the first rank.

Only then does `p0^2=Dm*P` imply `P` square. The rational square root `p0/d` of an integer is integral. Coprimality of positive `Dt,Dg` separately extracts their roots. This resolves the main potential circularity in the new construction.

After `Cy=delta*y^2`, the equation gives `Z^2=S^2*p0^2*f^2*y^2`, so `S|Ac` and `H|K^5`. There is no unsupported inference `H|K` at this stage.

### Ranks, short modulus, fifth-power projection, and source restoration

The retained nonodd strong-rank proof applies because the actual restored multiplier satisfies `c^2|I`; it does not assume `I/c^2` odd. Both auxiliary residues are exact. The first-Pell square is now available, so the pre-projection rank and ratio arguments are licensed.

For the short variant, `M=4q^4` satisfies `M>3R+1` and `M|2XY^2`. Consequently the first recurrence gives the signed congruence `epsilon*2n1=R+1 mod M`. The unchanged strip gives the main index greater than `n1`; the strong/auxiliary step-down gives main index `R`. The negative congruence branch is then impossible, and no wrap gives `2n1=R+1`. After orientation, the same exact recurrence modulo `XY` restores the old integer `h_old`. Conversely the canonical recurrence modulo `M` supplies the new integer `h`. The exact incoming proof of this step is now pinned locally as `source/INCOMING_LOWOPS_PROOF.md`, Section5.

With `R=2t+1`, `t>=24`, `x=|X|>=2^64`, the ratio bound is `|H|>x^(t+1)/2^t`. The signed projector and `H|K^5` give `H|Pi^5`, where `Pi=(sign(c)X-2^R)(2^R sign(c)X+1)`. Its strict upper bound is `2^(20t+20)x^10`, smaller than `|H|` since `43t-596>=436`. Hence `Pi=0`, yielding the exact power. The retained sign and half-binomial arguments then orient the outer witness. Fresh odd strong/auxiliary witnesses, rather than a false oddness claim about the incoming multiplier, restore an actual old signed Q41 zero before invoking the inherited calibration.

## 2. Completeness and fixed-witness quantifiers

The canonical outer witness fixes `Dm=d^2`, `Dt=tau^2`, the modulus-specific integer `h`, and `Budget>64`. Since `Dt=1 mod3`, `D*Dt` is positive and2 modulo3, hence nonsquare. Squaring a positive Pell unit supplies the guard `s,g>0`. The value `p0=d*tau*g` is then fixed.

Choose one strong pair with `4s*A*p0*c^2 | I`, and set `r=I/(A*p0*c^2)`. Every prime dividing `p0*s*r` divides this same fixed `I`. The retained supported-modulus theorem therefore applies to `p0*s*r`; it is the full p-adic isometry theorem, not an unjustified extension of a first-order congruence.

Select an intersective root `a0 mod sr`, then prescribe `T_old=p0*a0 mod p0*s*r`. The theorem supplies this auxiliary witness while keeping the strong pair fixed. Thus `T=T_old/p0` is integral, `T=a0 mod sr`, and `Ac/S` is integral. The equality `4I*T_old=4U*BP*T` restores precisely the new auxiliary expression. Finally `n=Ac/S+p0*f*y` makes the equation zero.

The valid order is outer data, guard, fixed `p0`, one strong pair and `r`, intersective residue, auxiliary witness, then `n`. Neither guard nor strong pair changes after the relevant residue is chosen.

## 3. Literal and exact-degree audit

`independent_audit.py` imports only the reviewer's earlier generic expression normalizer. It does not import or execute the producer's builder, checker, or any downloaded program. It independently transcribes and matches every named register and the entire output as free expressions, validates topology and all live vertices, and counts:

- Native:68 multiplications,23 additions,18 subtractions =109.
- Short:69 multiplications,23 additions,18 subtractions =110.

All eleven variables and six fixed ports occur in the live graph. Universal degree propagation gives upper bounds924/840. The term `-S^2 BP Df Cy` uniquely dominates `delta Z^2`. Independent multiplication of its full leading form gives

    2^36 3^7 q0^14 X0^64 Y0^106 k0^42 s^16 r^12 c^34 T^2,

with `q0=6 beta j`, `X0=12q0 w`, `Y0=2v q0^3`. Native `k0=hX0Y0`; short `k0=4h q0^4-q0^3(12wC-q0z)`.

Authentic nonzero coefficients independently verified:

- Native degree924: `2^960 3^677 beta^564` at `j^564 w^106 v^148 h^42 s^16 r^12 c^34 T^2`.
- Short degree840: `2^918 3^635 beta^564` at `j^564 w^64 v^106 h^42 s^16 r^12 c^34 T^2`.

The short coefficient is obtained by selecting `h^42`, uniquely choosing the h term in `k0^42`. Thus degrees are attained with the actual fixed coefficient tuple, not merely syntactic maxima or generic-parameter assertions. Four independent full modular univariate expansions at actual ports also attain the declared degree and match the complete leading form. Ten isolated graph corruptions are rejected.

All six raw payload hashes, byte counts and bit lengths are verified, together with byte identity of both the compressed payloads and binding file against the independently reconstructed frozen352 tuple. All source dependency pins are verified. This addendum audit does not claim a new independent execution of the full coefficient reconstruction recipe; the previously reviewed authentic tuple is transferred by exact byte identity.

Normal Python and `python -O` produce identical PASS receipts. `AUDIT.json`, `NORMAL_OUTPUT.json`, and `OPTIMIZED_OUTPUT.json` record hashes and witnesses.

## 4. Corrections and boundary

Two documentary defects found during review were corrected before acceptance: the auxiliary classification now uses `|rho| |V|`, not signed `rho |V|`; and the short-index citation now points to the actual pinned incoming proof rather than a source lacking that variant. Neither correction changes a literal polynomial.

No new mathematical defect remains in the reduction. The unbounded inherited native/compiler/calibration theorems remain explicit dependencies. Finite symbolic and modular checks establish polynomial identities, literal binding, degrees, and integrity, not those unbounded theorems or consistency itself.
