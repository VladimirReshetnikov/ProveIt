# Independent audit of the round12 integral norm centering

## Verdict and scope

PASS for the four frozen literal circuits in `../norm/`. The exact arithmetic counts and exact total degrees are:

| Circuit | Live binary operations | Exact degree |
| --- | ---: | ---: |
| `integer10_polar.json` | 471 | 1,245,324 |
| `integer10_center0.json` | 485 | 1,179,788 |
| `integer10_center1.json` | 496 | 1,114,252 |
| `integer10_center2.json` | 545 | 1,080,888 |

All have precisely the unrestricted integer inputs `t,g0,c0,k0,l,w,x,y,z,m`. Every internal register is a polynomial abbreviation, not a new existential variable. The only literal arithmetic instructions are binary addition, subtraction, and multiplication. Multiplication includes squaring and multiplication by a fixed scalar. Fixed integer leaves and reuse are free in the stated cost model.

This audit establishes the new algebra, the actual literal implementation, the coefficient and source-prefix bindings, and the short-guard proof. It does not supply a new kernel-checked formalization of the inherited source/compiler/refutation equivalence or the Pell/Lucas reliability and interpolation results. Those remain the explicit ordinary-mathematical dependencies recorded in `../norm/BASELINE_PROOF.md` and its pinned upstream sources. The degree/cost claims are neither global minima nor historical priority claims.

## 1. Independent executable verification

`check_independent.py` imports no producer builder, circuit helper, evaluator, or checker. It uses explicit exceptions, not Python assertions. Both normal and optimized (`python -O`) runs must succeed. The receipts record hashes of the exact four JSON circuits and actual coefficient payloads.

The checker independently does the following:

1. Validates the native source-port hashes, bit lengths, byte lengths, signed fixed-leaf encodings and hashes, all actual fixed-coefficient recipe evaluations, and the concrete radix and threshold. It verifies every supplied pinned upstream file. The historical parent-quartic JSON named by the inherited provenance manifest is not duplicated in this component; it is an inherited dependency, not a silently verified file.
2. Expands all 20,466 interactions of the actual three sparse kernels with the 31-coordinate code. At each of the 22 target exponents it checks the full polynomial identity, with source variables and all four fixed-parameter ports still symbolic. It verifies that the short-guard source and layout are exactly the ones used by these circuits.
3. Checks source row 4 exactly as `a-E-(N+1)s=0`, and checks that the coordinate `a` really is the unique weight-116 coordinate of this exact layout.
4. Verifies ten universal algebraic identities by exact coefficient cancellation over integer polynomial rings, including both first square defects, all three total square defects, the division-free correction identity, polarization, and the norm translation.
5. Checks every named register of each literal graph against independently written polynomial formulas by exact coefficient cancellation. Previously proved register identities are unfolded when common-subexpression reuse bypasses a register name. This is an exact full-prefix-to-output transcription check, not a finite sampling claim.
6. Checks all graph edges, allowed instruction kinds, the exact ten-variable interface, liveness of every node, operation counts, and independence of each translation polynomial from `m`.
7. Computes a syntactic degree upper bound and then evaluates its top homogeneous part at three separately chosen modular slope vectors, using the actual fixed integers. Nonzero resulting coefficients prove that the bound is attained. The primes, slope vectors and coefficients appear in the receipts.
8. Adds 448 signed/degenerate modular replays per candidate. These include moduli 2 and 3, each coordinate set to zero, and the all-zero input. The deepest correction is evaluated from its separately expanded integer polynomial. No inverse of 2, `A`, `C`, `xi`, or `Sigma` is used.

When the prior round is present, the audit also checks byte equality of the source, layout, kernels, and power plan against `round11/lucas_h1868`. The independent coefficient-target and literal checks above do not depend on importing prior programs.

## 2. The short guard: soundness ordering is essential

Write `Bcode=2^2134940 b^2`, `cap=b Bcode^116`, `e=C-KL`, and

    Delta = g(cap-g)K^2 - cap^2 e^2.

The assertion `Delta>0` alone does not justify a positive interval for `g` until `cap>0` is known. The actual soundness proof supplies that fact in the correct order.

The unchanged integer normalizations and modular identities give `a0=1 (mod 3)`, `a1=0 (mod 3)`, `b=Q=1 (mod 3)` and `gcd(b,Q)=1`. They do not need sign assumptions or the short-guard inequality. At a zero of the norm, the unchanged rational-square extraction first gives integer squares `a0,a1`, nonzero `Sigma`, and hence nonzero `z`.

Put `delta=9Delta-3` and `r=bQ`. The factors in

    a0 = r(1+delta*r*z^2)

are coprime. They are signed squares; because `r=1 (mod 3)`, `r` cannot be the negative of a square and is a positive square. Applying the same argument to the coprime factors of `r=bQ` shows that `b,Q` are positive squares. In particular `b>0`, `Bcode>0`, and `cap>0`. If `Delta<=0`, then `delta<=-3` and `z!=0`, so `1+delta*r*z^2<0`, a contradiction. Thus `Delta>0`.

Now the short-guard deductions are valid: `K!=0` and `g(cap-g)>0`; since `cap>0`, this means `0<g<cap`. The polynomial identity

    4g(cap-g) = cap^2-(cap-2g)^2 <= cap^2

then gives `4e^2<K^2`. These are at least as strong as the range and approximation conclusions required by the inherited decoding and saturated-Lucas reliability argument. In particular, after `l!=0` and the source lower bound for `Y` have been recovered, `|C|>|K|(|L|-1/2)>1` still excludes the exceptional small Lucas coordinates.

There is no cyclic invocation of the source bounds to prove `b>0` or `cap>0`: positivity is obtained by the square-factor and residue argument first.

## 3. Short-guard completeness is canonical, not a tuple bijection

In a canonical positive source witness, the verified row `a=E+(N+1)s` gives `a>=3`. Since `a` occupies weight 116, the packed integer

    g = sum_i (p_i-1) Bcode^w_i

satisfies `g>=2 Bcode^116`. The usual digit bounds `1<=p_i<=b`, distinct positive weights at most 116, and `Bcode>b` give `g<cap`. Also `Bcode^116>=b^2`, hence

    g^3 >= Bcode^348 >= b^2 Bcode^232 = cap^2.

The existing canonical approximation `|e|<|K|/(4g)`, with `K!=0`, therefore yields

    Delta/K^2 > g(cap-g)-cap^2/(16g^2)
               >= g-cap^2/(16g^2)
               >= 15g/16 > 0.

Here `cap-g>=1` uses integrality, and the last step uses `g^3>=cap^2`. No stronger Diophantine approximation theorem is needed. The subsequent Pell step still has `v_3(9Delta-3)=1` and therefore retains its nonsquare coefficient argument.

This establishes soundness on all signed assignments and completeness from canonical source witnesses. It does NOT claim that the old and new guards are equivalent for every input tuple. Thus guard replacement preserves the existence of solutions and the consistency equivalence, not a bijection with all round11 solution tuples. The producer corrected its initial ambiguous wording accordingly.

## 4. Polynomial translations are genuine integer bijections

After replacing the guard, retain the norm

    N(m) = ((Sigma*m-Theta)^2-Sigma^2(a0+a1))^2
           -4Sigma^4 a0 a1.

If integer polynomials `P,J`, independent of `m`, obey `a1=P^2+J`, put `Z=Sigma*m-Theta`. Exact expansion gives

    N(m+P) = (Z^2+2Sigma*P*Z+Sigma^2(a0-J))^2
             -4Sigma^2 a0 (Z+Sigma*P)^2.

Fixing the other nine arbitrary integers, the maps `m -> m+P` and `m -> m-P` are inverse bijections of the integers. This remains true when any of `A,C,xi,Sigma` is zero. No division or extra range condition appears. The sign of `P`, or of any intermediate polynomial, is irrelevant.

For center0 and center1 the audit verifies `DF=R0^2+J_DF` exactly, and consequently

    a1 = (R0*G*H)^2 + J_DF*G^2*H^2 - DF(H^2-1).

For center2 the audit substitutes `A=2h` first, where `h=halfA` is already an integer polynomial in the ten inputs. It then checks the displayed explicit correction polynomial `Q` lies in `Z[h,C,xi,B,y]` and satisfies

    4C^2*xi*A*Q = GH-GH0

as a polynomial identity, including at all zero factors. It verifies the entire final defect identity `a1=P^2+J` over that ring. The quotient notation is explanatory only. It would be incorrect to admit the formally divided expression as an arbitrary integer-coefficient polynomial in independent `A`; the actual circuit never does so.

The final one-operation reuse computes `uv=halfU*V`, `halfA=halfU+uv`, and `Phalf=U*uv`. The independent literal audit checks the new `uv` register and still compares `halfA` and `Phalf` with their original expanded formulas, proving that no polynomial changes. This replaces five binary operations by four and leaves every degree unchanged.

The affine `twice_k=b(6k0+4)` rewrite is also an exact identity `twice_k=2b(3k0+2)`, not a coordinate restriction or a change of the integer domain.

## 5. Exact degree, not only a circuit bound

The leading-coefficient certificates use authentic fixed numeral payloads, not independent symbolic ports. For each candidate the graph supplies an upper bound `D`, and the substitution `v_i=s_i*t` yields a nonzero coefficient of `t^D` modulo each recorded prime. Therefore the ordinary integer polynomial has total degree exactly `D`. A nonzero modular coefficient suffices because the corresponding integer coefficient cannot be zero.

For the deepest candidate the squared-inner term has upper degree 1,048,716, whereas the other term has degree

    4deg(Sigma)+deg(a0)+deg(a1)
      = 4(81,922)+294,382+458,818 = 1,080,888.

The modular certificates independently establish actual noncancellation. This confirms the stated barrier for further changes only to this same radical approximation; it is not a lower bound for other constructions.

## 6. Reproduction

From any working directory run:

    python path/to/norm_audit/check_independent.py
    python -O path/to/norm_audit/check_independent.py

The results are written to `INDEPENDENT_CHECKS.json` and `INDEPENDENT_CHECKS_OPTIMIZED.json`. The finite modular replays are regression checks; the mathematical claims rest on the exact identities and proof arguments above, together with the explicitly inherited source and Lucas/Pell dependencies.
