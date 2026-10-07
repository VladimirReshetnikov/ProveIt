# The second parameter-derivative of generalized Stieltjes constants at rational arguments: the s = 3 layer, its closed-form tables, and the negapolygamma unification

- Status: Report (verified experimental results + derived identities; honest
  literature attribution; numerics at the stated precisions; PSLQ/lindep with
  the corpus control + canary discipline)
- Created (UTC): 2026-06-28T18:55:35Z
- Repository HEAD: 2484d18eafaf9b9a643acddc880cad8d523dae37
- Requested by Vladimir: *"revisit generalized Stieltjes constants (including
  their derivatives and antiderivatives w.r.t. the parameter). Blagouchine
  gave some interesting formulae for rational parameters. Let's look for some
  new results close to that area."*
- Notation: `gamma_n(a)` from `zeta(s,a) = 1/(s-1) + sum_{n>=0} (-1)^n gamma_n(a)
  (s-1)^n / n!`; primes on `gamma_n` denote `d/da`; `zeta^(j)(s0,a)` is
  `d^j/ds^j zeta(s,a)` at `s = s0`; `A` the Glaisher–Kinkelin constant; `G`
  Catalan's constant; `beta(s) = L(s, chi_-4)` the Dirichlet beta function.
- Tools of record: [`stieltjes_s3.py`](../../tools/stieltjes_s3.py)
  (full verification battery, ALL GREEN), the exact-rank tool
  [`scratch/g1pp_grid_rank.py`](../../tools/scratch/g1pp_grid_rank.py), and the
  sporadic-hunt sweep [`stieltjes_s3_hunts.py`](../../tools/stieltjes_s3_hunts.py).

## 1. Executive summary

Blagouchine (J. Number Theory 148 (2015) 537–592) gave the closed-form theory
of the *first generalized Stieltjes constant* `gamma_1(p/q)` at rational
arguments. The parameter-**derivative** program in this corpus
([`stieltjes-derivative-relations__41afbe98f668.md`](stieltjes-derivative-relations__41afbe98f668.md))
showed that the `a`-derivative tower `gamma_n'(a)` lives one Hurwitz layer up,
at `s = 2` (Coffey 2009), mapped its lattice (rank `phi(q) - 1`) and its
character coordinate, and ran the first integer-relation sweep there — but it
stopped short of writing the *explicit closed-form table*, and it did not move
to the **second** parameter-derivative.

This report closes both gaps and adds a unification:

1. **Explicit closed-form tables** (apparently the first in the literature):
   `gamma_1'(p/q)` and `gamma_1''(p/q)` for every `p` at the elementary moduli
   `q in {1,2,3,4,6}`, each verified to `<= 1e-78`. Blagouchine tabulated
   `gamma_n` itself; the parameter-derivatives have not been tabulated.

2. **The s = 3 layer** — the rational-argument landscape of the *second*
   parameter-derivative `gamma_1''(a) = -2 zeta'(3,a) - 3 zeta(3,a)`:
   * the **character coordinate**
     `sum_k chi(k) gamma_1''(k/q) = -q^3 [ 2 L'(3,chi) + (3 + 2 ln q) L(3,chi) ]`
     (the level-3 analogue of the level-2
     `sum_k chi(k) gamma_1'(k/q) = q^2 [ L'(2,chi) + (1 + ln q) L(2,chi) ]`);
   * the **distribution row**
     `sum_{j<d} gamma_1''((a+j)/d) = d^3 gamma_1''(a) + d^3 ln d * psi''(a)`;
   * the **rank theorem**: the residual lattice dimension is `phi(q) - 1` on
     every grid `q = 3..30` (both parities — differentiation again destroys the
     reflection halving), measured by exact rational row reduction.

3. **The negapolygamma unification.** The functional equation pairs `s = 3`
   with `s = -2`, which is exactly the layer of the negative-order polygamma
   `psi^(-3)` ([`negapolygamma-landscape.md`](negapolygamma-landscape.md)). The
   odd-character atom `beta'(3) = L'(3, chi_-4)` that governs `gamma_1''(1/4)`
   is the **same** atom that appears in Wolfram's `PolyGamma[-3, 1/4]`; we
   verify `gamma_1''(1/4)` written through `psi^(-3)(1/4)` **exactly**, the
   bridge being the `k = 2` case of the corpus harmonic-number bridge law.

4. **First sporadic sweep at s = 3.** Over `{zeta'(3), beta'(3), L'(3,chi_-3),
   L'(3,chi_5)}` (PSLQ, dps 220, maxcoeff `1e12`, planted controls hit, random
   control rejected): **all negative** — every one is an independent genuine
   atom, mirroring the s = 2 finding that `beta'(2)` is uncatalogued.

The master identities are Coffey's; the rational-argument **landscape** (tables,
level-3 character coordinate, rank, the explicit `psi^(-3)` unification, the
hunt) is what is new here.

## 2. The two master identities (Coffey 2009)

From `d/da zeta(s,a) = -s zeta(s+1,a)` matched against the Laurent expansion at
`s = 1`:

```
gamma_1'(a)  = zeta'(2,a) + zeta(2,a)                       (s = 2 layer)
gamma_1''(a) = -2 zeta'(3,a) - 3 zeta(3,a)                  (s = 3 layer)
```

The second is the `a`-derivative of the first, since
`d/da zeta'(2,a) = d/ds[-s zeta(s+1,a)]|_{s=2} = -zeta(3,a) - 2 zeta'(3,a)` and
`d/da zeta(2,a) = -2 zeta(3,a)`. Both are instances of **Coffey's** all-orders
ladder (arXiv:0905.1111, Cor. 2),

```
gamma_l^{(j)}(a) = (-1)^l sum_k (-1)^k k! C(l,k) s(j+1,k+1) zeta^{(l-k)}(j+1,a),
```

with the `j = 1` Stirling row `s(2,k+1) = (1, -1)` giving the `s = 2` identity
and the `j = 2` row `s(3,k+1) = (2, -3, 1)` giving the general second-derivative
identity

```
gamma_n''(a) = (-1)^n [ 2 zeta^(n)(3,a) + 3n zeta^(n-1)(3,a) + n(n-1) zeta^(n-2)(3,a) ].
```

[Verified `n = 0..3` against a numeric second derivative of `mp.stieltjes`, and
the `n = 1` closed form against `d/da gamma_1'(a)`; residuals at the
finite-difference floor — `check_master_s3`.] The ground floor `n = 0` is
`gamma_0''(a) = -psi''(a) = 2 zeta(3,a)`, the tetragamma grid.

## 3. The explicit first-derivative table (q in {1,2,3,4,6})

With `zeta'(2) = zeta(2)(gamma + ln 2pi - 12 ln A)`, `G = L(2,chi_-4)` (Catalan),
`beta'(2) = L'(2,chi_-4) = 0.08158073611659...` (a genuine atom — see the s = 2
report), `L(2,chi_-3)` and `L'(2,chi_-3)` the conductor-3 odd-character atoms.
All entries verified to `<= 1.4e-79` (`check_table_gamma1_deriv`).

```
gamma_1'(1)   = zeta'(2) + pi^2/6
gamma_1'(1/2) = 3 zeta'(2) + pi^2/2 + (2/3) pi^2 ln2
gamma_1'(1/3) = 4 zeta'(2) + (2/3) pi^2 + (3/4) pi^2 ln3
                + (9/2) [ L'(2,chi_-3) + (1 + ln3) L(2,chi_-3) ]
gamma_1'(2/3) = 4 zeta'(2) + (2/3) pi^2 + (3/4) pi^2 ln3
                - (9/2) [ L'(2,chi_-3) + (1 + ln3) L(2,chi_-3) ]
gamma_1'(1/4) = 6 zeta'(2) + pi^2 + (7/3) pi^2 ln2 + 8 [ beta'(2) + (1 + ln4) G ]
gamma_1'(3/4) = 6 zeta'(2) + pi^2 + (7/3) pi^2 ln2 - 8 [ beta'(2) + (1 + ln4) G ]
gamma_1'(1/6) = 12 zeta'(2) + 2 pi^2 + (8/3) pi^2 ln2 + (9/4) pi^2 ln3
                + (45/2) L'(2,chi_-3) + (45/2)(1 + ln3) L(2,chi_-3) + 18 ln2 L(2,chi_-3)
gamma_1'(5/6) = (mirror: chi_-3 part negated)
```

The antisymmetric (odd-character) part is exactly the character coordinate:
`gamma_1'(p/q) - gamma_1'(1-p/q) = (1/?) sum_k chi(k) gamma_1'(k/q)
= q^2 [ L'(2,chi) + (1 + ln q) L(2,chi) ]` (here for the single odd character
present at `q = 3, 4`). At the s = 2 layer **both** `L(2,chi_odd)` (Catalan-class
value) and `L'(2,chi_odd)` (`beta'(2)`-class atom) are non-elementary, so each
small grid carries two odd-character atoms.

## 4. The s = 3 layer: landscape of the second parameter-derivative

**Distribution row** (only elementary-RHS row), `psi''(a) = -2 zeta(3,a)`:

```
sum_{j=0}^{d-1} gamma_1''((a+j)/d) = d^3 gamma_1''(a) + d^3 ln d * psi''(a)
```

[verified `d = 2,3,5`, residual `<= 1.0e-56` — `check_distribution_s3`].

**Character coordinate** (primitive `chi` mod `q`; uses
`sum_k chi(k) zeta(s,k/q) = q^s L(s,chi)` and its `s`-derivative):

```
sum_{k=1}^{q-1} chi(k) gamma_1''(k/q) = -q^3 [ 2 L'(3,chi) + (3 + 2 ln q) L(3,chi) ]
```

[verified for `chi_-3`, `chi_-4`, `chi_5` (quadratic, even) and the order-4
`chi_5` (quartic, odd), residual `<= 8.0e-59` — `check_char_coordinate_s3`].

**Rank theorem.** Exact `Fraction` row reduction of every distribution instance
on `{gamma_1''(k/q)}_{k=1..q-1}` (the same index combinatorics as the s = 2 tool,
weight `d^3` in place of `d^2`) gives, for every `q in 3..30`,

```
residual dimension = (q-1) - rank = phi(q) - 1
```

— one residual direction per non-principal Dirichlet character mod `q`, both
parities, identical to the s = 2 derivative case
([`scratch/g1pp_grid_rank.py`](../../tools/scratch/g1pp_grid_rank.py)). The
parity halving of the underived `gamma_n(p/q)` lattice (`phi(q)/2 - 1`, even
characters only) is absent at every derivative order: differentiation makes the
reflection object atom-bearing.

**Atom inventory at s = 3 (parity is flipped vs s = 2, because `s = 3` is odd).**

| sector | `L(3,chi)` (value) | `L'(3,chi)` (derivative) |
|---|---|---|
| principal | `zeta(3)` (value) | `zeta'(3)` (atom) |
| odd `chi` (`chi(-1) = -1`) | **elementary**: `beta(3) = pi^3/32`, `L(3,chi_-3) = 4 pi^3/(81 sqrt3)` | atom: `beta'(3)`, `L'(3,chi_-3)` |
| even `chi` (`chi(-1) = +1`) | atom (`zeta(3)`-class): `L(3,chi_5)` | atom: `L'(3,chi_5)` |

So at `q in {3,4,6}` the only odd character is present and its **value** is
elementary; the single genuine derivative-atom is `L'(3,chi_-3)` (or `beta'(3)`
at `q = 4`). This is the cleaner parity than the s = 2 layer.

## 5. The explicit second-derivative table (q in {1,2,3,4,6}) — new

`L(3,chi_-3) = 4 pi^3/(81 sqrt3) = 4 sqrt3 pi^3 / 243` (elementary). `beta'(3)
= L'(3,chi_-4) = 0.031577079457127...` and `L'(3,chi_-3) = 0.075275690627...`
are genuine atoms (Section 7). All entries verified to `<= 2.2e-78`
(`check_table_gamma1_deriv2`).

```
gamma_1''(1)   = -2 zeta'(3) - 3 zeta(3)
gamma_1''(1/2) = -14 zeta'(3) - (21 + 16 ln2) zeta(3)
gamma_1''(1/3) = -26 zeta'(3) - (39 + 27 ln3) zeta(3)
                 - [ 27 L'(3,chi_-3) + (81/2 + 27 ln3) L(3,chi_-3) ]
gamma_1''(2/3) = -26 zeta'(3) - (39 + 27 ln3) zeta(3)
                 + [ 27 L'(3,chi_-3) + (81/2 + 27 ln3) L(3,chi_-3) ]
gamma_1''(1/4) = -56 zeta'(3) - (84 + 120 ln2) zeta(3) - [ (3 + 4 ln2) pi^3 + 64 beta'(3) ]
gamma_1''(3/4) = -56 zeta'(3) - (84 + 120 ln2) zeta(3) + [ (3 + 4 ln2) pi^3 + 64 beta'(3) ]
gamma_1''(1/6) = -182 zeta'(3) - (273 + 208 ln2 + 189 ln3) zeta(3)
                 - [ 243 L'(3,chi_-3) + (729/2 + 216 ln2 + 243 ln3) L(3,chi_-3) ]
gamma_1''(5/6) = (mirror: chi_-3 part negated)
```

The odd-character block (containing both the elementary `pi^3` value-part and
the derivative-atom) flips sign under `p -> q - p`, in line with the character
coordinate of Section 4. At `q = 4` the elementary value-part is
`(3 + 4 ln2) pi^3` (this is `-(3/4) q^3 [ (3 + 2 ln q) L(3,chi_-4) ]` with
`L(3,chi_-4) = beta(3) = pi^3/32`, `q = 4`).

## 6. The negapolygamma unification (s = 3 <-> s = -2)

The functional equation pairs `s = 3` with `s = -2`. The `s = -2` derivative
layer is exactly where the negative-order polygamma `psi^(-3)` lives (its ladder
uses `zeta'(-2,z)`). Two facts tie the programs together:

**(a) Harmonic-number bridge law, `k = 2`** (corpus law from
[`negapolygamma-landscape.md`](negapolygamma-landscape.md); `H_2 = 3/2`):

```
L'(3,chi)/L(3,chi) + conj( L'(-2,chi)/L(-2,chi) ) = gamma + ln(2pi/q) - 3/2
```

[verified `chi_-4`, residual `1.1e-81` — `check_negapolygamma_bridge`]. This is
the `s = 3 <-> s = -2` analogue of the `C_q = gamma + ln(2pi/q) - 1` bridge of
the s = 2 report (there `H_1 = 1`).

**(b) The explicit shared atom.** `beta'(3) = L'(3,chi_-4)` appears with
coefficient `-64` in `gamma_1''(1/4)` (Section 5) **and** in Wolfram's
`PolyGamma[-3, 1/4]` via the flattened negapolygamma value

```
psi^(-3)(1/4) = 35 zeta(3)/(256 pi^2) + beta'(3)/(4 pi^3)
              + ln A / 4 + ln(2pi)/128 - gamma/128.
```

Eliminating `beta'(3)` gives `gamma_1''(1/4)` purely through `psi^(-3)(1/4)`,
`zeta(3)`, `zeta'(3)`, `pi^3`, `ln A`, `ln 2pi`, `gamma`, `ln 2` —
**verified exactly** (residual `2.8e-81`, `check_negapolygamma_bridge`). The
second parameter-derivative of a Stieltjes constant at `1/4` is thus an explicit
finite combination of a negative-order polygamma at `1/4`: the two corpus
programs are one landscape seen from the two sides of `s <-> 1 - s`.

## 7. The first sporadic sweep at s = 3

Protocol as in the companion reports (PSLQ; a candidate needs small coefficients
**and** residual at the precision floor; planted controls must hit; a random
control must be rejected). Sweep at `dps = 220`, `maxcoeff = 1e12`
([`stieltjes_s3_hunts.py`](../../tools/stieltjes_s3_hunts.py)).

**Controls (all behaved):** `L(3,chi_-3) = 4 pi^3 sqrt3/243` HIT (`max|c| = 243`);
`beta(3) = pi^3/32` HIT (exact); a random `1/pi` rejected.

**Open hunts (all negative):**

| hunt | target | basis | result |
|---|---|---|---|
| H1 | `beta'(3)` | `zeta(3), zeta'(3), pi^3, (.)ln2, (.)ln3, gamma(.)` | **none** |
| H2 | `L'(3,chi_-3)` | `zeta(3), zeta'(3), pi^3, L(3,chi_-3), (.)ln3, gamma(.)` | **none** |
| H3 | `L'(3,chi_5)` (even atom) | `zeta(3), zeta'(3), pi^3, L(3,chi_5), (.)ln5, gamma(.)` | **none** |
| H4 | cross `{zeta'(3), beta'(3), L'(3,chi_-3), L'(3,chi_5)}` | each other + `pi^3, zeta(3)` | **none** |
| H5 | cross-layer `beta'(3)` vs `beta'(2)` | `beta'(2), G, pi^3, zeta(3), pi^2, (.)ln2` | **none** |

So `zeta'(3)`, `beta'(3)`, `L'(3,chi_-3)`, `L'(3,chi_5)` are mutually
independent genuine atoms; no relation crosses the s = 2 / s = 3 derivative
levels — the s = 3 counterpart of "`beta'(2)` is uncatalogued". (`beta'(3) =
0.0315770794571273878872...` and `L'(3,chi_-3) = 0.0752756906272276296...`
have no OEIS entry.)

## 8. The q = 5 frontier (new even-character atoms)

At `q = 5` the residual dimension is `phi(5) - 1 = 3`. The quadratic character
`chi_5` is **even**, so at the odd value `s = 3` its value `L(3,chi_5)` is a
genuine atom (`L(3,chi_5)/zeta(3) = 0.71113502563950579...`, irrational), with
companion `L'(3,chi_5)`; the order-4 (odd) characters contribute an elementary
`pi^3`-multiple value `L(3,chi_5^{quartic})` and a derivative-atom
`L'(3,chi_5^{quartic})`. The per-value `gamma_1''(p/5)` is therefore not a tidy
rational combination of named constants; its clean presentation is the character
coordinate of Section 4 (`q^3 = 125`). These are the first explicitly new atoms
beyond the `q in {1,2,3,4,6}` elementary range.

## 9. Literature placement and honest novelty

- **Master identities — Coffey 2009** (arXiv:0905.1111; RMJM 44 (2014) 443–477),
  Prop. 1(ii) eq. (1.3) (`s = 2`) and Cor. 2 (1.7) (all orders, all layers; the
  `j = 2` row is the `s = 3` identity). **Connon 2019** has the `s = 2` identity
  and the `s = 0/1/2` antiderivative dictionary independently. Neither develops
  the rational-argument table at any derivative order.
- **Blagouchine 2015** (JNT 148) — the closed-form theory of `gamma_1(p/q)`
  itself (the underived constant). The parameter-derivative tables here are the
  "theorem one (and two) levels up".
- **The s = 2 landscape** — the companion corpus report
  [`stieltjes-derivative-relations__41afbe98f668.md`](stieltjes-derivative-relations__41afbe98f668.md)
  (rank, level-2 character coordinate, `C_q`-bridges, the s = 2 sporadic sweep,
  `beta'(2)` as a genuine atom). This report supplies the explicit s = 2 table
  it lacked and the entire s = 3 layer.
- **The s = -1/-2 / negapolygamma side — Miller–Adamchik 1998, Adamchik,
  Espinosa–Moll, Bailey–Borwein 2016**, and the corpus
  [`negapolygamma-landscape.md`](negapolygamma-landscape.md) (the `psi^(-n)`
  ladder, harmonic-number bridge law, the flattened `psi^(-3)(1/4)` value with
  its `beta'(3)` atom). The explicit `gamma_1''(1/4) <-> psi^(-3)(1/4)` identity
  is the new bridge instance.

**What is new here** (the survey's verdict): the explicit closed-form *tables*
for `gamma_1'(p/q)` and `gamma_1''(p/q)` at `q in {1,2,3,4,6}`; the level-3
character coordinate, distribution row, and rank theorem; the exact
`psi^(-3)` unification; and the first integer-relation sweep over the s = 3 atom
layer. The master identities and the harmonic-bridge machinery are attributed
above.

## 10. Artifacts and reproduction

```powershell
uv run --with mpmath python src/PolyLog/tools/stieltjes_s3.py        # full battery, ALL GREEN
uv run python src/PolyLog/tools/scratch/g1pp_grid_rank.py            # rank = phi(q)-1, q=3..30
uv run --with mpmath python src/PolyLog/tools/stieltjes_s3_hunts.py  # sporadic sweep (controls + open)
```

## 11. Follow-ups

1. The `gamma_2'(p/q)` and `gamma_2''(p/q)` tables (the second Stieltjes
   constant; `gamma_2''` brings `zeta''(3,.)` and `L''(3,chi)`).
2. The `s = k+1` towers for `k >= 3` (`gamma_1^{(k)}`): same rank `phi(q) - 1`,
   each paired by the FE with `s = -k` (the `psi^(-(k+1))` negapolygamma layer)
   through the `H_k` bridge — a uniform "derivative <-> negapolygamma" duality.
3. The even-character atoms `L(3,chi_5), L'(3,chi_5)` and the `q in {7,8,9,12}`
   grids (quartic/sextic atoms), with rigorous Arb exclusion bounds.
4. Promote the master identities, the level-3 character coordinate, the
   distribution row, and the `psi^(-3)` bridge into the identity stores as
   certificate-grade entries.
