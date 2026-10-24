# Literal split116 source and nine-coordinate equation

The current numerical candidate is
[compact54-sharp](candidates/split116-compact/compact54-sharp/README.md):
nine positive variables, 473 live binary operations, degree 1,910,404.
Its natural translation has 480 operations. The complete coefficient tuple
is fixed by the candidate's signed payload bindings; all four native ports
come from the same package-54 instance. Its height is `H=2^864014`, radix
floor `2^864026`, and threshold scale `2^6912197`.

Lean now checks the complete arithmetic equivalence between the literal
split source and the nine-coordinate expression. The native source-to-K215
calibration is still open. This is therefore a source-equivalent candidate,
not a replacement for the closed `ExplicitZFC` consistency endpoint.

## Equation and witness domain

Write the nine strictly positive integer unknowns as

```
b, g, h, s, w, C, i, j_plus, n,
```

and put `j=j_plus-1`. The internal CRT index may be zero. Let `D0,D1,D2`
be the three fixed kernel polynomials, and `w_r,q_t` their fixed input and
target positions. Their 7+39+43 records are copied exactly in
[the pinned data](data/split59/README.md), and their Lean definitions are in
`SplitKernelData59`. Use the following integer polynomial registers:

```
B = 2^864026*b^2
ell = sum_r B^w_r
targets = sum_t B^q_t
Gs = D2(B)*(ell+g)^2 + D1(B)*(ell+g) + D0(B)
Mask = B^117-1-(b-1)*ell
S = g+B^117*(2*Gs+targets)
T = Mask+B^117*(B-2)*targets
L = b*B^2279
R = L*(S+T+1)-S-1
N = 2^6912197*b*B^1201
t = b*B^116
```

The remaining ratio and finalizer registers are

```
U = N^2*w             Y = N^2*s
M = R*Y               P = 2*M^2*U
K = R+1+h*(P-1)       a = M*(U+1)
B1 = 2*R+1            W = b*w
J = 4*a-5             Q = 3*W*C-2*(W^2-1)
D = (a^2-1)*C^2+1     E = i*J*D*C^2
F = (a^2-1)*E^2+1     G = a+F*(C*D+1-a)
H = C+F*(B1+j*C)      I = (G^2-1)*H^2+1
k = i*J*C             V0 = P*K
V1 = k*(8*D^2-4*D-1)*G*H
m = K^2*(4*t-g)-16*t*(C-K*Y)^2
Omega = J*m
Theta = J*(n+W^2)+Q-Omega*(V0+V1)
A0 = (P^2-1)*K^2+1
A1 = D*F*I
```

The final equation is

```
(Theta^2-Omega^2*(A0+64*A1))^2-256*Omega^4*A0*A1 = 0.
```

All powers have fixed natural exponents. Every register is a polynomial
abbreviation; the displayed sums and registers add no unknowns. For nine
natural unknowns, replace the eight positive coordinates other than `j`
by their successors and use the natural internal `j` directly. This agrees
with translating the positive coordinate `j_plus` by its successor.

The finite replay identifies the literal 473/480-operation DAGs with this
schedule and proves the stated degree by cancellation-aware certificates.
The Lean arithmetic proof below uses finite polynomial sums. Its evaluator
has not yet been identified with the counted shared DAG by a Lean theorem.

## Checked proof chain

`SplitGeometry59` checks the 31 distinct input weights, 22 distinct targets
and 22,544 same-degree isolation interactions. The weights have maximum
116, the targets maximum 2129. Cross-degree labels may coincide.

`SplitCertificate59` independently transcribes the authoritative old-z
parent source, proves both invertible row operations and their permutation,
and extracts twice each resulting row at its target. Its source is the
expanded `parent_source.json`, not the inherited package-52 comparison file.

`SplitKernelData59` binds every literal coefficient and proves degrees at
most 1719, 2027 and 1929, with top quadratic coefficient 1. Its all-record
height bound is strictly `2*Bcap*Kcap` when the four native ports satisfy
their stated boxes and `Kcap>=16*Bcap`. `SplitKernels59` identifies those
literal polynomials with the exact extracted channels over every
commutative ring. Thus the compact54 port boxes imply `H=2^864014`
without a separate coefficient-height assumption.

`SplitSourceWords` proves positivity before the weak cap and exact agreement
of natural/integer word and mask expressions. `SplitSourceContract` gives
the calibrated binomial test iff bounded source coefficients vanish.
`SplitSourceExistence` constructs the explicit cofinal power of two
`b=2^(sum z_r+1)`, eliminating all code-size assumptions, and supplies the
exact nine-coordinate positive/natural translations.

Finally,
`SplitNineSource59.exists_natural_zero_iff_source_compact54` proves

```
(exists x : Fin 9 -> Nat, naturalValue ports 864014 x = 0)
  iff
(exists z : Fin 31 -> Nat, forall k, sourceRows ports (z+1) k = 0)
```

with precisely these four hypotheses:

```
0 <= beta < 2^429959,   0 <= K0 < 2^434054,
0 <= MC < 2^429959,     0 <= MF_source < 2*2^429959.
```

The source's row 10 equals `-7` at the all-one tuple, independently of
the ports. Hence every source zero has a nonzero low digit, which supplies
the strictly positive outer `g`. This boundary needs no native assumption.
Negating the existence equivalence is also checked. All audited endpoints
use only the standard Lean axioms; there are no proof placeholders.

## Remaining semantic endpoints

The numerical payloads and their bit lengths are independently replayed
finite artifacts. The theorem above quantifies over integer ports satisfying
the boxes; it does not itself read the compressed numerical payloads.

The authentic native/compiler proof must still identify the particular
whole-tuple source with blank K215 halting, then use the existing refutation
endpoint. The signed auxiliary Pell step-down is now checked separately in
[NATIVE_PELL_STEP_DOWN.md](NATIVE_PELL_STEP_DOWN.md), with main classification
and bootstrap hypotheses explicit. Neither this local arithmetic bridge
nor the source-coding theorem supplies the remaining native semantics.

An object-language ZFC proof of consistency iff unsolvability remains a
separate task, as described in [OBJECT_ZFC.md](OBJECT_ZFC.md). No global
simplicity minimum is claimed.
