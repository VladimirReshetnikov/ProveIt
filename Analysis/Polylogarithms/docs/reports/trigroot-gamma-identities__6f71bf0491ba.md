# Trig-root Gamma identities: the mechanism and a census

- Status: Report (research finding)
- Created (UTC): 2026-06-10T19:35:39Z
- Repository HEAD: 59dc3bed576cf5dd4fd3f37c8dd036d5618caa56
- Tools: [`../../tools/gamma_reducer.py`](../../tools/gamma_reducer.py)
  (lattice reducer), [`../../tools/scan-trigroot-gammas.py`](../../tools/scan-trigroot-gammas.py)
  (the census scanner), [`../../tools/gamma-reducer.wl`](../../tools/gamma-reducer.wl)
  (rendering/verification)
- Prompted by Vladimir's
  `Γ(2/7)Γ(11/42)/Γ(1/21) = 8 sin(π/7)·√(π sin(π/21) sin(4π/21) sin(5π/21)) / (2^(1/42)·7^(1/3)·3^(9/28))`
  — *"some mathematicians were surprised by it initially, before they
  realized the mechanism."*

## 1. The mechanism, in lattice terms

In log-Γ coordinates every reflection/multiplication consequence is a
ℚ-linear relation. When the lattice solve expresses a target `log Γ(k/N)`,
the elimination may pass through a combination in which the target appears
with **multiplicity D > 1** — i.e. the relation natively proves
`Γ(k/N)^D = (elementary) · (Γ-monomial)`. Dividing by D puts coefficient
`1/D` on the elementary `log sin` atoms, and exponentiating yields a
**D-th root of a sine product**; positivity of all factors fixes the branch.
So the root is a property of the *derivation path*, not of the value: the
same `Γ(11/42)` carries a square root in the harvested spelling and **cube
roots** in the lattice's basis (see §3) — both exactly correct.

The surprise dissolves further at grids whose sines are radical-expressible:
for `N = 30, 60` the renderer collapses `√(sin···)` into golden-ratio
radicals and nothing looks trig-rooted at all. The phenomenon is only
*visible* when the sine arguments have large totient (21, 39, 78, …), where
no real-radical form exists (casus irreducibilis).

## 2. Census (denominator grids N ≤ 200, primitive arguments)

856 lattice reductions carry fractional `log sin` coefficients. By root
degree D (LCM of the coefficient denominators):

| D | 2 | 3 | 4 | 6 | 8 | 16 |
|---|---:|---:|---:|---:|---:|---:|
| rules | 616 | 46 | 106 | 26 | 42 | 20 |

Square roots are commonplace (Vladimir's example's class); cube, fourth,
sixth, eighth and even **sixteenth** roots of sine products occur. Demanding
*integral* Γ-exponents (so only the trig part is rooted, as in the prompt
example) leaves exactly **10 rules, all D = 4**, at
`Γ(71/78)`, `Γ(85/156)`, `Γ(65/114)`, `Γ(167/198)` and conjugate-numerator
siblings. The D = 16 monsters live on the N = 168 grid with 26 sines under
the radical.

## 3. Verified showpieces

All verified to 30+ digits via `GammaLatticeReducer`GammaReduce` (and
independently by the Python reducer's mpmath check).

**The fourth-root champion** — three Γ-factors, eighth-power cosine roots
(N = 78; φ(78) = 24, so none of the cosines collapse to radicals):

```
Γ(71/78) == 2·2^(55/312) π √(cos(π/78)) cos(π/39)^(1/8) cos(π/26)^(3/4)
            cos(2π/39)^(5/8) cos(4π/39)^(11/8) (cos(π/13) sec(7π/78))^(3/8)
            Γ(1/39) / (13^(1/48) cos(5π/78)^(1/4) cos(3π/26)^(3/2)
            cos(5π/39)^(7/8) cos(11π/78)^(5/8) Γ(2/39) Γ(5/78))
```

**Cube roots on the prompt's own grid** — the lattice's reduction of the
very same `Γ(11/42)`:

```
Γ(11/42) == 7^(1/6) √π Γ(1/42) Γ(1/21) (sec(π/42) sec(π/21))^(2/3)
            sec(π/14)^2 (cos(2π/21) sec(5π/42))^(1/3)
            / (8·2^(5/21) 3^(3/7) Γ(2/21) Γ(3/14))
```

— same value as the prompt identity (which we verified RootReduce-exactly
against the FT table earlier), square root in one derivation path, cube
roots in another.

**The D = 4 family with integral Γ-exponents** (the closest structural
analogues of the prompt example at higher degree): `Γ(85/156)` over
`{Γ(1/20)⁻¹, Γ(7/60), Γ(3/20), …}` with fourth roots of 15 sines, and
`Γ(65/114)`, `Γ(167/198)` likewise (renderings in the scanner output;
all verified).

## 4. Reproduction

```powershell
# census over N <= 200
python src/PolyLog/tools/scan-trigroot-gammas.py
# render + verify any single value
wolframscript -code 'Get["src/PolyLog/tools/gamma-reducer.wl"]; Needs["GammaLatticeReducer`"]; GammaReduce[71/78]'
```
