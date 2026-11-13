# Package 72 P13 (13 positive, degree 28, 98 operations): iPRA endpoint plan

Opened 4 November 2026. Claude session, at Vladimir's choice ("Package 72 P13
here"). The source is
[`72-congruence-sextic/positive13`](../../con-zfc-diophantine-forms/72-congruence-sextic/positive13/PROOF13.md),
with circuit `p13_degree28.json`, SHA-256
`1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49`, on the
whole compact44 tuple.

## Why no cheap reduction exists

- **The witness transform fails.** On a free-J zero,
  `r = τ − ell − k − s + t(k·qm + 1)`, where `τ ≈ ell + k/2` and
  `t = Bt/(q−1) = q(z_old − 1)`. So every free-J zero has `z_old ≥ 2`. P13
  deliberately allows `z_old = 1`. Some P13 zeros therefore have no free-J zero
  with the same transport data, and P13 must reach halting through the
  shared halting chain itself.
- **The two carriers are parametrized differently.**
  - first carrier: P13 has `Z = M0(ell + r) + (q−1)Y − q³Bt`, with no folded
    `k − k·Bt`;
  - main carrier: P13 has `Dhat = β·Dstar`, with `M = 4q²Y` and `S = 4qY`;
  - strong equation: P13 has the normalized `f² − ΔI² = 1`, with `I = c²i`,
    where free-J has the ordinary `I² = Δ(f² − 1)`;
  - `J` is recovered from `As = 0` by rational-root integrality.

## The shared halting chain: measured interface

`hzgraph.py` (this session's scratchpad) computes the call graph of literal-zero
hypotheses reachable from `FixedGraphMarkedHaltDraft.graph_halts`:

- 60 theorems;
- 54 only forward `hz`;
- 6 are mathematical leaves.

| Leaf | Conclusion | P13 source |
| --- | --- | --- |
| `FreeJExactOrdinary.exact_ordinary_indices` | first and main indices, `pi = R`, `2j = R+1`, Pell coordinates | §6, signed auxiliary index ⇒ `p = R` |
| `FreeJFirstTransport.freej_first_factor_transport` | `(F+α)A + Fq < qA`, `F+α < q` | `C ≥ 1` |
| `FreeJGraphCongruenceExplore.first_pair_mod` | `((F+α)A + Fq) % Jβ = qA % Jβ` | §5, `q−1 ∣ Bt` |
| `FreeJPowerFinish.graph_power` | `X = 2^R` | Pell growth plus main projection, with `gcd(q,H) = 1` |
| `FreeJPowerProjection.graph_projection` | `q ∣ 3X`, `q ≤ 3X` | §6, `q ∣ X` |
| `FreeJRootBinding.first_scaled_norm` | `|Z|² = M²(1 + ell(ell+k))` on the free-J `Z` syntax | replace it by its consumers' conclusions (`q³ ∣ Y`, the first-root quotient) |

The non-leaf `first_quotient` (`k = R+1+4XY²t`) and `growth` (`2^R < Y`)
are also needed by `graph_power`.

## Phases

1. **Interface.** Define `Compact44Facts p v`, the conjunction of the leaf
   conclusions, minus `first_scaled_norm` (its consumers' conclusions
   replace it). Retype `hz` in the 54 forwarding theorems, and turn leaf calls
   into field projections. Prove `facts_of_literal` from the existing leaves.
   Rebuild the chain and every dependent endpoint (95-op through 87/51).
   - This pays off beyond P13: every compact44 equation that proves `Facts`
     gets halting.
   - It changes promoted modules beyond their imports, so it needs a new
     review record.
2. **P13 soundness.** P13 zero ⇒ `Compact44Facts` at the pseudo-valuation
   `![J, F, α, f−1, T, X, Y, r', η, ζ, n, γ']`. The chain's `hv` is used only at
   the indices the leaves need, which must be checked. The steps:
   1. §4: `As = 0` ⇒ `b ∣ Nf` ⇒ `J = 3j+1`; integral `R`; packing bounds.
   2. §5: `M0 ∣ Z` ⇒ `q³ ∣ Y`, `q−1 ∣ Bt`, the first norm with `|τ|`.
   3. §6: main root `g`; `gcd(S,H) ≤ 3`; Pell classification; strong rank
      `c ∣ m`; the signed auxiliary index (package 61 `SIGNED_INDEX_LEMMA`) ⇒
      `p = R`; `2n = R+1`; `q ∣ X`.
   4. growth `2^R < Y`, projection ⇒ `X = 2^R`.
   5. §7: transport facts.
3. **P13 converse.** Halt ⇒ P13 zero, from the canonical halt data
   (`FreeJHaltModelZero`: `J = rep N` with `N` odd ⇒ `J ≡ 1 (mod 3)`). Take
   `f0 = f − j`, `T` and `u` from the squared-modulus reconstruction, and
   `r = τ − ell − s + t`, `γ = γ_old + v/M − w`.
4. **Endpoint.** The `IPRAOrdinary12Chain` helpers, the record, the docs.

Proposed size: Phase 1 is about 60 module edits, mechanical and verified by
rebuild. Phases 2–3 are about 15–25 new modules.

## Status and decisions (4 November 2026)

**Phase 1 is built as a parallel chain, not by editing in place.**

- *Why not in place:* `CompactSymbolicPorts` and `CompactSymbolicGraphDigits`
  feed the low-byte, mask and beta infrastructure. Editing them in place
  would rebuild 218 modules.
- *What was done instead:*
  - [`tools/factsgen.py`](tools/factsgen.py) writes `Compact44/Facts/<File>.lean`
    for the 45 files holding the 49 forwarders, listed in
    [`tools/forwarders.txt`](tools/forwarders.txt).
  - Each copy re-opens the original namespace and restates the theorem as
    `<name>_facts` over `CompactLeafFacts.LeafFacts`.
  - No promoted module changes.
  - [`tools/hzgraph.py`](tools/hzgraph.py) derives the forwarder list, and
    [`tools/c44dag.py`](tools/c44dag.py) checks the import DAG: there are no
    cycles, because the leaf closure contains no forwarder file.
- *The transport field is weakened.* It is `0 < q − (F+α)` only. All three
  forwarder uses take `.2`, and the strict `Fq < C·A` fails at `z_old = 1`.

**Phase 1 landed (`3eb716174d`).** `CompactLeafFactsHalt.halts_of_facts` gives
`LeafFacts` at the compact44 ports, at a positive valuation, ⇒ internal halt.
Its consistency check is `literal_halts`.

**Phase 2: P13 zero ⇒ `LeafFacts`, module by module.** The pseudo-valuation is
`v' = ![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]`, so `1 + Jβ = q`.

1. `P72Graph`: the 98-gate graph, generated and checked from JSON. The
   derived leaves are `.constant`s computed from `p 0`. Then
   `output = A0² + A1² + Aa² + As²` (gate order `((A0²+A1²)+Aa²)+As²`), and
   a four-squares zero split.
2. Evaluation lemmas over a generic `CommRing` for `Z`, `A0`, `Dhat`, `A1`,
   `Aa`, `As`, plus the pair representation of `Z` (as in
   `FreeJRootBinding.root_rep`):
   `pos = M0(ell+r) + (q−1)Y + q³·qF`, `neg = q³(qK0+X)C`.
3. §4: `NfV := 3βf0 + q − (β+1) > 0`. `scaled_quotient` gives `NfV = b·f`
   and `f² = 1 + ΔI²`. Then `f ≥ f0`, `j = f − f0`, and
   `q = 1 + β(3j+1)`.
4. §5: `A0 = 0` ⇒ `|Z|² = M0²(…)` ⇒ `M0 ∣ |Z|` ⇒ `pos ≡ neg (mod M0)`.
   - Mod `q³`: `q³ ∣ (q−1)Y`; the Bézout certificate
     `q³ − (q−1)(q²+q+1) = 1` gives `ydiv`.
   - Cancelling `q³`: `qF ≡ AC (mod q−1)`, which is `pairMod`.
   - The `transport` gap is `C > 0`.
5. §6: the main root `g` from `A1 = 0`, via `Dhat = β·Dstar`. Then Pell
   classification, strong rank, `signed_half_index_of_facts` (with
   `i' = Δi`), `p = R`, `2n = R+1`, `v = k − R − 1`, and `q ∣ X`. These give
   `indices` and `projection`.
6. Growth `2^R < Y` and the main projection `X ≡ 2^R (mod H)`, with
   `gcd(q,H) = 1`, give `power`.

**Phase 2 progress.** These modules are landed:

- `P72Graph` (`51d96df89e`);
- `P72Root.strong_root` and `first_root` (§4, §5);
- `P72Main.main_root` (`458ea8ff9d`).

The remaining §6 order, with tree lemmas:

1. `P72Aux`: `Aa = 0` with `Nf = bf`, `Vhat = L·V` and `yhat = L(V+u)`. This gives
   `Qa·V² − (Qa−1)(V+u)² = 1`, where `Qa = Δ(f²−1) = (Δic²)²`, and
   `z = absdiff (f²·Tc) (f²R + c)`.
2. Indices:
   - first: `ArithmeticPellFirstNorm.positive_parameter_solution Q τ k`, with
     `Q = XY²` and parameter `2(Q−1)+1`;
   - main: `ArithmeticPellClassification.solution_index a g c`.
3. `μ ∣ v`: `g0 = gcd(S,H)` from `gcd_certificate_exists`, then
   `S/g0 ∣ v` via `unit_certificate_cancel`.
   - `g0 ∣ 3`, because `qH − (X+1)S = 3q` and `gcd(q,H) = 1`.
   - That uses `q ≡ 2 (mod 3)`, from `β % 3 = 1` (a fact about the ℕ numeral).
   - `μ ≥ 4qY/3 > q⁴ > R + 1`; `R < q⁴` comes from the packing bounds.
4. `k ≡ 2n (mod 4Q)` (Pell first recurrence) and `μ ∣ 4Q` give
   `2n ≡ R+1 (mod μ)`. So `n ≥ 25`, `m > n`, and `hbig` follows from
   `large_of_six`.
5. `2R < c`; then `signed_half_index_of_facts`, with `i' = Δi`, `rp = R`,
   `rn = 0`, gives `m = R`. Then `2n = R+1`, and `first_transport` gives
   `k = R+1+4Qt`.
6. `q ∣ X`: since `M ∣ v`, `M ∣ HSX`, so `q ∣ HX`, so `q ∣ X`. This is
   `projection`.
7. `power`: `g = X + ac + Hγ'`, with `γ'` integral; the Pell projection
   mod `H`; and growth `2^R < Y`. The model is `FreeJPowerFinish` and
   `FreeJPowerGrowth` (math cores to be located).

**Phase 2 done (`f9ec93c720`).** Modules:

- `P72Mu`, `P72Window`, `P72Early`, `P72Exact`, `P72Power` — §6, from
  `218e4741e6` to `e8a8acae90`;
- `P72Facts.facts_ports` — the assembly into `LeafFacts`;
- `P72Facts.halts` — a positive P13 zero ⇒ machine 215 halts.

**Phase 3 detail (data available after `CompactHaltFirstGamma.halt_first_gamma`).**
Take the halt context as in `FreeJHaltModelZero.halt_positive_zero_of_ports`:

- `N = haltLength T`, `u = 590069N`, `q = 2^u`, `R = rank`, `X = 2^R`, `w_X = 2^{R−u}`;
- `Y = sY·q³`;
- `SeedRelations`: `τ = E·n + k − R`, `τ² = 1 + (EY)(EY+1)k²`, `d = X + ac + γ_old·H`,
  `d² = 1 + δ(a)c²`, `c = ψ_a(R)`, `R = 2r+1`, `k = 2ψ_B(r+1)`;
- `PositiveAuxData`: `f = χ_a(Rc)`, `ψ_a(Rc) = icc`, the normalized strong norm, `I = Δicc`,
  `y = ψ_{I−2}(R)`, `f²cT = w + c + f²R` (so `V = w`), `I²w² + y² = 1 + I²y²`, and
  `Δ(f²−1) = c⁴(Δi)²`;
- `FirstData`: `(qK + X)C = qF + (q−1)(qz)`, so `Bt = (q−1)·qz`;
- `GammaData`: `k = R + 1 + (Yq²)t`, `γ + w_X = γ_old + t`.

The P13 witnesses, in the order `F α C f0 i T X Y r η ζ u γ`:

- `Fw`, `alpha`, `Cw`, from the packing;
- `f0 = f − j`, where `J = rep N = 3j+1`. This uses `N` odd (`power_p_odd`) and
  `q ≡ 2 (mod 3)`;
- `i`, `T`, `X = 2^R`, `Y`;
- `r = τ − ell − s + qz`, positive since `τ > ell + s` (because `k > 2s`);
- `η`, `ζ`;
- `u = y − w`, positive since `y = ψ(R) ≥ 2`;
- `γ = γ_old + t/4 − w_X`, which needs `4 ∣ t`. This follows from
  `k − R − 1 = 4XY²s'` (`residue_quotients`), and `v/M = t/4 ≥ w_X·q² > w_X`.

The residuals vanish identically:

- `A0 = M0²(τ² − 1 − ell(ell+k))`;
- `A1 = β²M²(d² − 1 − Δc²)`;
- `As = b²(f² − 1 − Δ(c²i)²)`;
- `Aa = b²L²(y² − I²(y² − w²) − 1)`.

The ports: `CompactSymbolicPortProjections.beta`, `kernel`, `low` and `high`
(as used by `CompactSymbolicModelUnconditionalIff`). The rank:
`graph_rank_of_packing` at a dummy 12-valuation `![J, F, α, …]`.

**Phase 3: halt ⇒ P13 zero.** Split `FreeJHaltModelZero.halt_positive_zero_of_ports`
at its `zero_of_model_data` call. The model data already carries P13's forms:
the normalized strong `f² = 1 + Δ(icc)²`, `Maux = Δicc`, `V = auxw` (via
`hlit`), `Bt = (q−1)·qz`, and `τ = seedTau`. The witnesses are:

- `C = q − F − α`;
- `f0 = f − j`, which needs `J ≡ 1 (mod 3)`. Here `J = rep N` with
  `N = haltLength T = 581197^(2T+4)` odd (`power_p_odd`), and
  `q = 2^(dN) ≡ 2 (mod 3)`, `β ≡ 1 (mod 3)`;
- `u = y − V`;
- `r = τ − ell − s + qz`, positive since `τ − ell > k/3 > s`;
- `γ = γ_old + v/M − w`.

**Phase 2 map (2011 templates).** P13's normalized strong equation implies
the ordinary one with `i' = Δi`, since `(i'c²)² = Δ(f²−1)`, and `Maux = i'c²`.
So these 2011 lemmas apply as stated:

- `AdaptiveGap85GenericSignedHalfIndex.signed_half_index_of_facts`;
- `ArithmeticPellResidueAux.square_mod_one_of_relaxed_auxiliary`;
- `ArithmeticPellResidueAux.signed_residue_of_relaxed_auxiliary`.

`ArithmeticAdaptiveExactIndices2011.exact_indices_of_facts` shows the
assembly. Its `Comparison` input is tied to the 2011 literal's folded first
carrier, and that carrier has the same `z_old ≥ 2` obstruction. So P13 needs
its own producers:

| P13 producer | 2011 template |
| --- | --- |
| first and main norms from `A0` and `A1` | `ArithmeticAdaptiveScaledNorms2011` |
| Pell classification into indices `n` and `m` | `ArithmeticAdaptivePellIndices2011.indices_of_quotients` |
| rank window | `ArithmeticAdaptiveRankWindow2011` |
| `2n ≡ R+1 (mod q⁴)` | `ArithmeticAdaptiveIndexComparison2011` |
| strong and auxiliary norms | `ArithmeticAdaptiveStrongNorm2011`, `ArithmeticAdaptiveAuxNorm2011` |
