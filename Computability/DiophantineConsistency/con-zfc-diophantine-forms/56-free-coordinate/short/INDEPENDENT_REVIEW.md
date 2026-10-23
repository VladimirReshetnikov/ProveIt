# Independent mathematical review of Q54 and Q46

Reviewed 23 October 2026 by a separate mathematical review agent within this AI-assisted collaboration. This is not external human peer review and not a new Lean/Rocq compilation or checked object-language ZFC derivation.

## Reviewed claims

The reviewer read `PROOF.md` and the literal construction logic in `build_and_audit.py`, comparing the argument with the incoming squared-modulus proof and degree44 minimum-norm proof at repository snapshot `4b4349064a750ba6347293b55874a7f92abdd0db`.

The local equivalence and the existence reconstruction are mathematically valid as stated. The new equations are

```
Q54 = N0^2 + Na^2 + Ws^2 + (N1*Nk*Nt-1)^2 - 2,
Q46 = N0^2 + N1^2 + Na^2 + Ws^2 + (Nk*Nt-1)^2 - 3,
```

with the definitions, strictly positive domain, and coherent package31 coefficient tuple in `PROOF.md`.

## Independent checks of the mathematical steps

1. Let `n=XY^2`. The first norm is `tau^2-n(n+1)k^2`, because `L=XY^2 k`. Since `n(n+1)` lies strictly between successive squares, the norm cannot vanish for positive `k`. The stated elementary negative-Pell descent excludes -1 for `n>=2`. Thus `N0^2>=1`, with equality exactly at `N0=1`.
2. For `y0=V+e`, the auxiliary identity is `Na=UV^2-(U-1)y0^2`. If `U>0`, then `U>=2`; its vanishing would force the consecutive positive integers `U,U-1` both to be squares, unless both roots vanish. The latter is impossible because `e>0`. Hence `Na!=0`. If `U=0`, then `Ws=I^2>=81`, so the block cannot have its minimum 1. Equality `Na^2+Ws^2=1` therefore gives `Ws=0`, `Na=+/-1`. The equality `U=I^2` makes `Na` a square residue modulo4, excluding -1.
3. The residue obstruction for the main norm is valid: `Delta=(a+2)^2-1` is 0 or3 modulo4, and `D^2-Delta*c^2` cannot be3 modulo4. Thus `N1` cannot equal -1.
4. Consequently Q54=0 forces `N0=Na=1`, `Ws=0`, and `N1NkNt=1`. The last identity makes each factor a unit; the main-norm obstruction forces `N1=1`, leaving `NkNt=1`. These are exactly the equality conditions of Q46. The argument is tuplewise and independent of compiler semantics.
5. The quotient replacement has the exact all-value identity `V_new(f,T)=V_old(f,fT)`. Thus every new positive zero maps to an old positive zero. The proof correctly avoids asserting that every old quotient is divisible by f.
6. Completeness correctly begins with a canonical normalized witness and transfers it to ordinary strong using `i_ordinary=Delta*i_normalized`. This explicitly retains `f^2=1 mod c`, `gcd(c,f)=1`, and `I^2=Delta(f^2-1)`. The congruence `f^2=1 mod c` must not be inferred from the ordinary strong equation alone; the stated canonical construction supplies it.
7. The odd Pell polynomial identities yield the fresh `V=-c mod f^2` and `V=-R mod c` when `R=3 mod4`. Together with the retained congruences, they make `(V+c+Rf^2)/(cf^2)` a positive integer. This gives precisely the new quotient. The positive Pell ordinate y has `y>V>1`, since `(I^2-1)(y^2-V^2)=V^2-1`; therefore the new gap `e=y-V` is positive.
8. The degree argument is consistent: `N1NkNt` has degree27 (18+7+2), so its square uniquely reaches54; the auxiliary gap norm has degree23, so its square uniquely reaches46 in Q46. The displayed leading forms are nonzero for beta>0. Exact implementation counts and coefficient hashes are delegated to the accompanying finite auditor, rather than inferred merely from this proof review.

## Boundaries retained

The final consistency equivalence imports the ordinary native compiler, its whole coherent coefficient tuple, the ordinary Pell/rank interfaces, and the calibrated K215/refutation endpoint. This review does not replace those sources by finite evaluation tests. It establishes the new local mathematical transformations and their stated composition with those interfaces. The incoming 66-operation and degree44 alternatives remain distinct comparison points; these new results do not beat both of those metrics simultaneously.
