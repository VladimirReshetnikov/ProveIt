# A globe can be flattened with no distortion at almost every point

Nov 23, 2026 · @Vladimir Reshetnikov

## Theorem

A sphere cut along one meridian has a continuous, one-to-one flat map that is free of distortion at almost every point.

Let S be the unit sphere with one closed meridian removed (a half great circle from pole to pole, the cut every rectangular world map makes). For every ε > 0 there are an open set Ω ⊂ R² and a continuous one-to-one map F from S onto Ω, with continuous inverse, such that:

1. area(Ω) < (1 + ε)·4π, so the sheet is barely larger than the sphere.
2. There is a set Z ⊂ S of zero area such that at every p ∈ S ∖ Z the map is rigid to first order: F(q) = F(p) + Lₚ(q − p) + o(|q − p|) as q → p in S. Here Lₚ is linear and |Lₚv| = |v| for every v tangent to S at p.
3. F(S ∖ Z) has area exactly 4π, and F⁻¹ is likewise differentiable with length-preserving differential at each of its points.
4. F stays within 2ε of the classical sinusoidal projection (lon, lat) ↦ (lon·cos lat, lat).

So at almost every point of the globe the scale is exactly 1 in every direction, and all angles and infinitesimal areas are exact.

### Why it looks impossible

Standard cartography rules out any projection that keeps both angles and areas ([source](https://Www.Wikipedia.org/wiki/User:Jacobolus/stereographic_projection)), and Gauss's Theorema Egregium forbids an isometry on any open patch. Both statements remain true here: the good set S ∖ Z has full area but contains no open patch, and F is not Lipschitz. The zero-area set Z is smeared over the remaining sliver of the sheet, of area less than ε·4π.

## Proof: setup and the key proposition

The theorem reduces to building one function u of longitude and latitude.

Use longitude and latitude (x, y) ∈ D = (−π, π) × (−π/2, π/2) and Φ(x, y) = (cos y cos x, cos y sin x, sin y). The vectors ∂Φ/∂x and ∂Φ/∂y are orthogonal with lengths cos y and 1.

**Proposition.** For 0 < ε < 1 there is a continuous function u on the closed rectangle D̄ with:

- (i) u(x₂, y) − u(x₁, y) ≥ cos y · (x₂ − x₁) for x₁ < x₂;
- (ii) |u(x, y) − (cos y + ε)x| ≤ ε;
- (iii) at almost every (x, y) ∈ D, u is differentiable with ∇u = (cos y, 0).

On each parallel, x ↦ u(x, y) is a staircase: slope cos y almost everywhere, yet a larger total rise. The difficulty is ∂u/∂y = 0: staircases at different latitudes have different slopes but must agree to first order at almost every point. The naive product cos y · x + ε·s(x), with s a Cantor function, has ∂u/∂y = −x sin y ≠ 0.

## Step 1: one refinement stage

Each stage freezes the previous function on thin latitude strips and re-profiles it along longitude.

Put γₙ(y) = cos y + ε·4⁻ⁿ and θₙ = 2⁻ⁿ⁻³. Each γₙ is 1-Lipschitz and γₙ₋₁ − γₙ = 3ε·4⁻ⁿ. Start with u₀ = γ₀(y)·x.

Hypothesis (Hₙ): uₙ is continuous on D̄ and uₙ(x₂, y) − uₙ(x₁, y) ≥ γₙ(y)(x₂ − x₁) for x₁ < x₂.

Given uₙ₋₁, pick integers N, M and set h = hₙ = π/N, ℓ = ℓₙ = 2π/M, θ = θₙ, with h ≤ 3ε·4⁻ⁿ and ℓ ≤ h. Then:

- **Grid.** yⱼ = −π/2 + jh, strips Jⱼ = \[yⱼ, yⱼ₊₁\] with midpoints ȳⱼ, and xₖ = −π + kℓ.
- **Tile slopes.** Jⱼ⁺ is the set of latitudes within θh of Jⱼ, and bⱼ is the maximum of γₙ over Jⱼ⁺.
- **Frozen profile.** Pⱼ(x) = uₙ₋₁(x, ȳⱼ).
- **New profile.** On each period \[xₖ, xₖ₊₁\], set Qⱼ(xₖ + t) = Pⱼ(xₖ) + bⱼt for 0 ≤ t ≤ (1 − θ)ℓ. On the rest of the period Qⱼ is affine and returns to Qⱼ(xₖ₊₁) = Pⱼ(xₖ₊₁).
- **Cores.** If y ∈ Jⱼ is at distance ≥ θh from every interior grid point (the yⱼ with 1 ≤ j ≤ N − 1), set uₙ(x, y) = Qⱼ(x).
- **Layers.** If |y − yⱼ| ≤ θh for some 1 ≤ j ≤ N − 1, set uₙ = (1 − t)Qⱼ₋₁ + tQⱼ with t = (y − yⱼ + θh)/(2θh).
- **Tiles.** These are the open rectangles (xₖ, xₖ + (1 − θ)ℓ) × Jⱼ°, where Jⱼ° is the open core of strip j.

## Step 2: five facts

Each stage keeps the slope bound, makes the tiles exact, and moves the function very little.

**(a) (Hₙ) holds.** Every point of Jⱼ⁺ is within h of ȳⱼ, so bⱼ ≤ γₙ(ȳⱼ) + h ≤ γₙ₋₁(ȳⱼ). By (Hₙ₋₁), Pⱼ rises by at least bⱼℓ per period. The first piece of Qⱼ uses bⱼ(1 − θ)ℓ of that rise, so the second piece has slope ≥ bⱼ.

Thus all slopes of Qⱼ are ≥ bⱼ. In a core, bⱼ ≥ γₙ(y). In a layer, y ∈ Jⱼ₋₁⁺ ∩ Jⱼ⁺, so both bⱼ₋₁ and bⱼ are ≥ γₙ(y). Continuity is clear.

**(b) Tiles are exact.** On a tile, uₙ = c + bⱼx with gradient (bⱼ, 0), and 0 < bⱼ − cos y ≤ 2hₙ + ε·4⁻ⁿ for y ∈ Jⱼ.

**(c) Global closeness.** sup |uₙ − uₙ₋₁| ≤ ωₙ₋₁(ℓₙ) + ωₙ₋₁(hₙ), where ωₙ₋₁ is the modulus of continuity of uₙ₋₁. Indeed, on a period Pⱼ and Qⱼ are increasing with equal end values, and the midpoints used at height y are within h of y.

**(d) Local closeness (n ≥ 2).** Let T′ be a stage-(n − 1) tile with slope b′, and let z ∈ T′ be at distance ≥ ℓₙ + hₙ from ∂T′. Then |uₙ(z) − uₙ₋₁(z)| ≤ ηₙℓₙ with ηₙ = 2hₙ₋₁ + 3ε·4⁻ⁿ.

*Proof of (d).* The periods and midpoints ȳⱼ used at z lie in T′, so there Pⱼ is affine with slope b′ and equals uₙ₋₁(·, y). From (a) and (b):

```latex
\gamma_{n-1}(\bar y_j) - 3\varepsilon 4^{-n} \;\le\; b_j \;\le\; \gamma_{n-1}(\bar y_j) \;\le\; b' \;\le\; \gamma_{n-1}(\bar y_j) + 2h_{n-1}
```

So 0 ≤ b′ − bⱼ ≤ ηₙ. On a period, Qⱼ − Pⱼ vanishes at both ends and is piecewise affine, so |Qⱼ − Pⱼ| ≤ (b′ − bⱼ)ℓₙ.

**(e) Tiles fill up.** Let ρₙ = θₙℓₙ. The points of D not lying in a tile at distance ≥ ρₙ from its boundary have area ≤ 7θₙ·area(D). Each grid cell contains a tile of size (1 − θ)ℓ by at least (1 − 2θ)h, and trimming a border of width ρₙ ≤ θh leaves a fraction ≥ (1 − 3θ)(1 − 4θ).

## Step 3: choice of scales

The scales shrink fast enough that every later stage is negligible at the scale of the current tiles.

Put ρ₀ = ε. At stage n take N, M so large that hₙ ≤ 3ε·4⁻ⁿ and ℓₙ ≤ hₙ, and also:

- (S2) ℓₙ + hₙ ≤ ρₙ₋₁/2;
- (S3) ωₙ₋₁(ℓₙ) + ωₙ₋₁(hₙ) ≤ 2⁻ⁿρₙ₋₁.

Then ρₙ decreases to 0, and the sum over n of sup |uₙ − uₙ₋₁| is at most ε. So uₙ → u uniformly, u is continuous, and (ii) holds. Property (i) follows from (Hₙ) since γₙ ≥ cos y.

## Step 4: differentiability almost everywhere

Almost every point sits deep inside a tile at every late stage, and there u is differentiable with gradient (cos y, 0).

By (e) and Borel–Cantelli (the θₙ are summable), almost every p = (x₀, y₀) lies, for all n ≥ n₀(p), in a stage-n tile Tₙ at distance ≥ ρₙ from ∂Tₙ. Fix such p. Take q = (x, y) with r = |q − p| small, and choose n ≥ n₀ with ρₙ₊₁/2 ≤ r < ρₙ/2.

Then q ∈ Tₙ, and by (S2) both p and q are at distance ≥ ℓₙ₊₁ + hₙ₊₁ from ∂Tₙ. Write uₙ = c + βₙx on Tₙ. Then:

```latex
u(q)-u(p)-\cos y_0\,(x-x_0) = (\beta_n-\cos y_0)(x-x_0) + \big[(u-u_n)(q)-(u-u_n)(p)\big]
```

By (b), the first term on the right is at most (2hₙ + ε·4⁻ⁿ)·r. By (d) and (S3), at each z ∈ {p, q}:

```latex
|(u-u_n)(z)| \;\le\; \eta_{n+1}\ell_{n+1} + \sum_{m\ge n+2} 2^{-m}\rho_{m-1} \;\le\; \eta_{n+1}\ell_{n+1} + 2^{-n-1}\rho_{n+1}
```

Since r ≥ θₙ₊₁ℓₙ₊₁/2, this is at most (2ηₙ₊₁/θₙ₊₁ + 2⁻ⁿ)·r, and ηₙ₊₁/θₙ₊₁ ≤ 108·ε·2⁻ⁿ.

So the left side is o(r), which is (iii). The key point is that stage n + 1 perturbs uₙ inside old tiles by far less than the size of the new tiles, because the slope it corrects is already almost right.

## Step 5: from u to F

Apply the Proposition with ε/3 and define F(Φ(x, y)) = (u(x, y), y); the four items of the theorem follow.

- **Homeomorphism.** By (i), F is injective and maps D onto Ω = {(s, y) : u(−π, y) < s < u(π, y)}, which is open. If (sᵢ, yᵢ) → (s, y) with preimages xᵢ and x, then cos y · |xᵢ − x| ≤ |u(xᵢ, y) − s| → 0 by uniform continuity, so the inverse is continuous.
- **Item 2.** At a point of (iii), DF is the diagonal matrix diag(cos y, 1). It sends the orthonormal frame (∂Φ/∂x)/cos y, ∂Φ/∂y to (1, 0), (0, 1).
- **Item 1.** By (ii), area(Ω) ≤ ∫ (2π cos y + 2π·ε/3 + 2·ε/3) dy < 4π(1 + ε).
- **Item 4.** By (ii), |u − x cos y| ≤ (1 + π)ε/3 < 2ε.
- **Item 3.** On each parallel, u(·, y) is increasing with derivative cos y on a set of full length. An increasing function with derivative c on a set A maps it to a set of length c·|A|, and Fubini gives area ∫ 2π cos y dy = 4π. A homeomorphism differentiable at p with invertible derivative has an inverse differentiable at F(p).

This completes the proof. Three stages of the construction were also instantiated numerically, and (a), (b) and (d) held on random samples.

## Limits of the result

The map cannot be Lipschitz, and this construction cannot remove the wasted sliver.

- **Not Lipschitz, necessarily.** If F were Lipschitz on a patch, then in a conformal coordinate it would be a Lipschitz almost-everywhere solution of the Cauchy–Riemann equations. It would then be holomorphic, hence a smooth isometry, contradicting Gauss.
- **The sliver is necessary for this construction.** If parallels go to horizontal segments at the correct height and no area is wasted, each u(·, y) must be absolutely continuous. That forces u = x cos y + c(y), whose shear cannot vanish almost everywhere.
- **Open here.** Whether ε = 0 is attainable by other maps with classical differentiability is not proved.

## Novelty and nearest known results

A literature search did not find this statement. That does not certify it is unrecorded, and the proof above does not depend on it.

| Nearest result | What it gives | What it lacks here |
| --- | --- | --- |
| [Goldstein, Grochulska and Hajłasz](https://arxiv.org/abs/2312.13078) | A positive-determinant matrix field as the derivative of a diffeomorphism off a set of small measure; a nonsingular field as the approximate derivative of a homeomorphism almost everywhere | Only approximate differentiability, so no classical first-order rigidity as in item 2; its application to the sphere is unchecked |
| Alberti; Moonens and Pfeffer ([as summarized by David](https://arxiv.org/pdf/1502.00694)) | A continuous, almost-everywhere differentiable scalar function with any prescribed gradient field | No monotonicity, hence no one-to-one map |
| Gromov ([as revisited by Petrunin](https://arxiv.org/pdf/1003.5621)) | Maps of any Riemannian surface into the plane that keep the length of every curve | Lipschitz, but far from injective |

Together these give a trichotomy for flattening a sphere. Of the three properties Lipschitz, one-to-one, and isometric almost everywhere, any two can hold but not all three. The theorem above is the "one-to-one and isometric almost everywhere" corner, which is the one a map of the Earth needs.
