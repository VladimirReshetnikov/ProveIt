# Exact modular evaluation of the fixed coefficient tuple

`coefficient_residues.py` evaluates the four exact fixed coefficients
without constructing their full binary numerals. It belongs beside
`PRUNED_T4_CONSTANTS.json` and `pruned_t4_windows.json` in the package's
`compiler/` directory. It requires only the Python standard library.

## Interface

```
python3 coefficient_residues.py --modulus 1000000007
python3 coefficient_residues.py --verify --receipt coefficient_residue_verification.json
```

The optional `--data-dir DIRECTORY` points to the unchanged recipe and
tile files when the evaluator is run from a different location. The
reusable function is

```
coefficient_residues(modulus, data_dir=None)
```

It returns a dictionary with exactly the circuit ports `Bm1`, `Kconstant`,
`MC`, and `MF`, each reduced to the interval `[0,modulus)`. The modulus
must be a positive Python integer. The value 1 is supported and gives
four zero residues. No assumption that the modulus is prime, odd, or
coprime to 2 or to a geometric-series denominator is made.

**MF denotes the shifted source port**, not the native high mask:

`Bm1=B-1, Kconstant=D_C+B*D_R, MC=M_C, MF=M_F^native+B-1`.

For modulus 1,000,000,007 the returned tuple is

```
Bm1      = 139741305
Kconstant= 984538569
MC       = 604047481
MF       = 147133133
```

These values permit direct modular evaluation of every included arithmetic
circuit at the actual fixed coefficient tuple. They are residues of the
fixed integers, not a replacement coefficient recipe.

## Authentication and exact-instance binding

Every public evaluation authenticates both complete files before using
their data. The evaluator embeds these SHA-256 digests:

| Data | SHA-256 |
|---|---|
| Recipe | `9a314993a5ca523dc5f56d9e175540fc990341f39d0862b3aed4c29612dc853e` |
| Ordered tiles | `baa3d2b5296b818b2e6488c1b06fda29e405d9b4cf5dd19a3c38fbdd1ba658d7` |

It also checks the recipe's binding identifier and scalar fields, the tile
count and range, the distinguished Start/forbidden ordering, uniqueness,
and the remaining lexicographic order. This is deliberately a calculator
for this one exact tuple. A changed recipe, changed tile order, or even a
byte-level reformatting is rejected unless the evaluator is explicitly
updated and reviewed for that new data. The machine-table and transition
hashes are authenticated as fields of the frozen recipe; this calculator
does not regenerate the tile predicate or repeat the machine audit.

## Mathematical justification

Reduction modulo any positive integer N is a ring homomorphism. Hence it
commutes with each fixed finite sum, product, subtraction, and
nonnegative-integer power in the coefficient recipe. All exponents used
here are fixed ordinary integers. The two astronomical bases are evaluated
as

`rho_mod=pow(2,78125,N)` and `B_mod=pow(2,152587890625,N)`.

The built-in modular exponentiation never first constructs either full
power. The identity `78125*1953125=152587890625` is checked.

For the clause coefficients, the evaluator first forms the residues
`A0^j mod N` for `0<=j<=2835` by repeated multiplication, where `A0=2^13`.
Each of the 5,252 authenticated tiles supplies its literal selector weight.
The copy and anchor weights are then added exactly as in section 4 of
`PRUNED_T4_PROOF.md`. Both dummy positions remain in the support even
though their clause weights are zero. The resulting fixed support has
7,014 elements and maximum position `Emax=82873`.

Define the reverse polynomial

`H(z)=sum(v_e*z^(Emax-e), e in E)`.

It is evaluated by sparse Horner arithmetic. Every gap exponent is
nonnegative, so no inverse is needed. The two clause bands in D_C satisfy
the exact polynomial identity

```
sum(v_e*(rho^(T1-e)+rho^(T2-e)), e in E)
  =(rho^(T1-Emax)+rho^(T2-Emax))*H(rho),
```

with `T1=771293`, `T2=937043`. All remaining bare D_C terms and
`D_R=rho^605107` are evaluated separately. This proves the regrouped D_C
and K calculations.

For geometric sums let `S_n(z)=sum(z^j,0<=j<n)`. The evaluator uses

`S_(r+s)(z)=S_r(z)+z^r*S_s(z)`

and repeated doubling. It never divides by z-1. In particular the formula
remains valid when z-1 is zero or a nonunit modulo N. The support sum
excluding selector position 1 is

```
S_5252(rho)-rho
 +S_439(rho)*(rho^8764+rho^8325+rho^7886+rho^7008)
 +rho^10520+rho^10521
 +rho^11839+rho^23678+rho^35517+rho^82873.
```

Subtracting this sum and the additional `2*rho^10520` from B-1 is exactly
M_C. This support calculation does not discard a position merely because
its clause weight happens to vanish modulo the supplied N.

Likewise the native high mask is evaluated as

```
mu*(rho^771293+rho^937043)
 +S_439(rho)*(rho^8325+rho^613871+rho^613432)
 +rho^35517+rho^82873+4,
```

with `mu=A0-2+sum(A0^j,1<=j<=2835)`. The final source shift adds B-1.
These identities establish that every returned value is the residue of
the exact integer defined in the authenticated coefficient recipe.

## Verification receipt

`coefficient_residue_verification.json` records an implementation audit:

* A separately written literal finite-sum implementation uses direct
  powers `pow(2,78125*exponent,N)` and independently constructs the weights.
  It shares neither sparse Horner, grouped clause bands, geometric sums,
  nor the production weight-construction function. Seven internal/final
  values agree at each of 12 moduli, including 1, powers of 2, odd
  composites, and primes: 84 exact comparisons.
* The binary geometric-sum routine agrees with directly materialized
  miniature powers in 150 small cases, including zero and nonunit bases.
* The independently known low congruences hold:
  `MC=2 mod4`, `MF_native=4 mod8`, `MF_source=3 mod8`,
  `D_C=D_R=3 mod5`, `2D_C-D_R=3 mod5`, and `Kconstant=4 mod5`.
* Altering either authenticated file by one whitespace byte is rejected.
  Zero, negative, Boolean and noninteger moduli are rejected.
* All checks were executed under `python -O`; validation uses explicit
  exceptions and is not disabled by optimization.

An independent read-only review by the compiler-audit agent checked every
support interval, weight, band, exclusion, dummy subtraction and mask
shift against the recipe, as well as both hard-coded file hashes. A
separate execution modulo 97 returned
`(Bm1,Kconstant,MC,MF)=(1,87,19,66)`.

These checks verify the arithmetic evaluator and its data binding. The
mathematical compiler semantics and K215 calibration remain the cited
theorems; neither a finite residue check nor this evaluator supplies a
halting computation or a proof of ZFC consistency.
