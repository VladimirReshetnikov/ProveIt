# A sextic in 34 unrestricted integers

The source is the literal package-64 quartic Q41 at repository commit
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`. Its ordinary mathematical
equivalence to existence of a finite ZFC refutation is inherited from
`integer41/PROOF41.md` and its named arithmetic, native-compiler, and
machine-calibration dependencies. No new semantic premise is added.

## Exact equation

All 34 variables of `sextic34.json` range independently over the integers.
The four coefficient ports are the entire same fixed package-64/source-34
tuple. Define `q=beta*J+1`, `k=eta+zeta`, `C=q-F-alpha`, and `H=4*a+3`.
The polynomial is the sum of squares of these 19 residuals:

1. `L-q^2+1`.
2. `2u^2-4w_scale*q`.
3. `a-E-(2v_scale+1)*q*(L+1)`.
4. `E*(2u^2+1)-2u^2*a`.
5. `c-eta-(a-E)*k`.
6. `tau^2+(2tau-k)*E*(c-eta)-1`.
7. `D-2u^2-gamma*H`.
8. `D^2+2a*c*D-H*c^2-1`.
9. `k-1-h*E-(((q-1)*(q-F)+alpha)*L+(MC+q*MF)*J)`.
10. `(K0+4w_scale)*C-F-z*(q-1)`.
11. `F2-f^2`.
12. `f*o-c-j*c+k-1-h*E`.
13. `g+F2*o^2-2f*o*c+c^2-y^2`.
14. `I-(2r+1)*c^2`.
15. `I^2-(a^2+4a+3)*(F2-1)`.
16. `y^2-I^2*g-1`.
17. `F*alpha-1-FA_pos1^2-FA_pos2^2-FA_pos3*(FA_pos3+1)`.
18. `F*C-1-FC_pos1^2-FC_pos2^2-FC_pos3*(FC_pos3+1)`.
19. `eta*zeta-1-eta_zeta_pos1^2-eta_zeta_pos2^2-eta_zeta_pos3*(eta_zeta_pos3+1)`.

The named `tau` and `D` coordinates are new integer coordinates, not the
source's original roots. Every other surviving coordinate is unchanged.

## Integer zero-set bijection

Given a zero of the new system, restore the deleted source coordinates by

```
P = k+E(c-eta),  X = 2u^2,  N = q(L+1),
C2 = c^2,  Delta = a^2+4a+3,  V = fo-c,  Baux = I^2,
tau_old = tau+E(c-eta),  D_old = D+ac.
```

All restorations are integer polynomials, so they impose no omitted
divisibility condition. The seven defining source rows for
`P,X,N,C2,Delta,V,Baux` vanish identically. Each other source row is one
listed residual, except for the auxiliary difference row
`V^2+g-y^2`. Its restored value differs from row 13 by precisely

```
row13 - restored_old_row = o^2*(F2-f^2).
```

Row 11 is retained; hence the old and new difference rows vanish together.
This is a reversible elementary row operation in the polynomial ideal,
not a division and not a relaxation of integrality.

The source main norm is transformed exactly by

```
(D+ac)^2-(a^2+4a+3)c^2-1
   = D^2+2acD-(4a+3)c^2-1.
```

The first norm is transformed exactly by putting `B=E(c-eta)`:

```
(tau+B)^2-(k+B)B-1 = tau^2+(2tau-k)B-1.
```

Conversely, take any integer zero of Q41, forget the seven defined
registers, and set

```
tau = tau_old-E(c-eta),  D = D_old-ac.
```

The same identities prove all new residuals zero. These two maps are
inverse on the complete integer zero sets. This proves the reduction
without any positivity hypotheses or new Pell arguments.

## Count and degree

There are 41-7=34 variables and 26-7=19 residuals. Each residual has
total degree at most three when the four coefficient ports are fixed.
The retained auxiliary norm `y^2-I^2*g-1` is the only residual containing
both `I` and `g`. Consequently the coefficient of `I^4*g^2` in the sum
of squares is exactly 1. The resulting fixed polynomial therefore has
exact total degree six, after authentic coefficient specialization too.

The key improvement over the package-62 sextic35 is to keep `F2=f^2`
as a lifting register while deleting the product coordinate `V=fo-c`.
The quadratic term `f^2 o^2` becomes the cubic term `F2 o^2` by an
explicit ideal-preserving row operation. Simultaneous shearing of the
two original norm roots permits elimination of `Delta` without exceeding
residual degree three. The source's lower-variable delayed-sign guard
is kept intact. The result is a finite-catalogue improvement, not a
global minimum or a claim of a large breakthrough.

## Verification scope

`build_sextic34.py` uses exact sparse polynomial arithmetic and verifies
every deleted row, every restored row, the single nontrivial row
correction, all variable liveness, all residual degrees, and the exact
degree certificate. It expands the full sum of squares into 368 terms
when coefficient ports are symbolic. These checks establish algebra,
not the inherited unbounded native/Pell consistency equivalence.

Thus ordinary mathematics formalizable in ZFC proves

```
(exists an integer zero of this sextic) iff (exists a finite ZFC refutation).
```

Negation gives the requested consistency equivalence. No newly supplied
end-to-end proof-assistant certificate is claimed.
