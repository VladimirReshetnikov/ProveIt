import IPRADerivations.Core.OrderCertificates

/-!
# Exact families of hyperbox surface distances

Packet: `geometry/hyperbox_surface_ipra_2026-11-20`, `hyperbox_surface.tex`, Section "Exact families and a strict
comparison in every dimension" and "Closed fixed-vertex solution for a prism with a cubical base".

* `hypercube_twofacet` ("The hypercube": "`(4+n−2)a²` bounds the num 2-facet formula (`eq:twofacet`)"): for
  coordinate differences `d_k ≤ a`, `(d_i + d_j)² + ∑_{k} d_k² ≤ (4 + m) a²` over any list of `m` further
  coordinates;
* `short_side_average` ("One short side, all others equal": "Averaging the num 2 squared lengths gives at most
  `u² + v² + h(u+v) + h² + K` … since `r² + (h−r)² ≤ h²` for `0 ≤ r ≤ h`"): for `t, s ≤ h`,
  `(u+t)² + (v+s)² + (u+(h−t))² + (v+(h−s))² ≤ 2(u² + v² + h(u+v) + h²)`;
* `prism_difference` (`sec:prismfixed`): for `t = (C+1)/(2C)`, `R² = C² + dt² + 2Ct`, `L² = C² + d + 2`,
  `4C²(R² − L²) = (C − 1)(4C² − 3dC − d)`, cleared of `4C²`;
* `prism_example` ("For the four-dimensional `1×1×1×5` prism the off-vertex point is `(3/5, 3/5, 3/5, 5)` and
  `E = √802/5`"): `25 R² = 802 > 25 L² = 750` at `d = 3`, `C = 5`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.Hyperbox.ClosedFamilies

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `∑ d_k²` over a list of coordinate differences. -/
def sqsum : List (PTm n) → PTm n
  | [] => zero
  | d :: ds => d * d + sqsum ds

theorem sqsum_le (ds : List (PTm n)) {a : PTm n} (h : ∀ d ∈ ds, Γ ⊢[PRAAx] le d a) :
    Γ ⊢[PRAAx] le (sqsum ds) (num ds.length * (a * a)) := by
  induction ds with
  | nil =>
    show Γ ⊢[PRAAx] le zero (num 0 * (a * a))
    ipra_le 0
  | cons d ds ih =>
    show Γ ⊢[PRAAx] le (d * d + sqsum ds) (num (ds.length + 1) * (a * a))
    have hd := h d List.mem_cons_self
    have hs := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    ipra_le sl hd * (𝔟 a + 𝔟 d) + sl hs using
      push_cast; ring

/-- The hypercube num 2-facet bound `(d_i + d_j)² + ∑ d_k² ≤ (4 + m) a²`. -/
theorem hypercube_twofacet {di dj a : PTm n} (ds : List (PTm n)) (hi : Γ ⊢[PRAAx] le di a)
    (hj : Γ ⊢[PRAAx] le dj a) (h : ∀ d ∈ ds, Γ ⊢[PRAAx] le d a) :
    Γ ⊢[PRAAx] le ((di + dj) * (di + dj) + sqsum ds) ((num 4 + num ds.length) * (a * a)) := by
  have hs := sqsum_le ds h
  ipra_le (sl hi + sl hj) * (2 * 𝔟 a + 𝔟 di + 𝔟 dj) + sl hs using
    push_cast; ring

/-- `(u+t)² + (u+(h−t))² ≤ 2u² + 2uh + h²` for `t ≤ h`. -/
theorem plate_pair {u t h : PTm n} (ht : Γ ⊢[PRAAx] le t h) :
    Γ ⊢[PRAAx] le ((u + t) * (u + t) + (u + monus h t) * (u + monus h t)) (num 2 * (u * u) + num 2 * (u * h) + h * h) := by
  ipra_le 2 * 𝔟 t * 𝔟 (monus h t) with (2 * 𝔟 u + 𝔟 h + 𝔟 t + 𝔟 (monus h t)) * natEq (eq_add_of_le ht)

/-- Averaging over the num 2 end plates. -/
theorem short_side_average {u v t s h : PTm n} (ht : Γ ⊢[PRAAx] le t h) (hs : Γ ⊢[PRAAx] le s h) :
    Γ ⊢[PRAAx] le ((u + t) * (u + t) + (v + s) * (v + s) +
        ((u + monus h t) * (u + monus h t) + (v + monus h s) * (v + monus h s)))
      (num 2 * (u * u + v * v + h * (u + v) + h * h)) := by
  have p := plate_pair (u := u) ht
  have q := plate_pair (u := v) hs
  ipra_le sl p + sl q

/-- `4C²(R² − L²) = (C − 1)(4C² − 3dC − d)` with `2Ct = C + 1`. -/
theorem prism_difference (C d : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 4 * (C * C) * (C * C) + d * ((C + ZT.natLit 1) * (C + ZT.natLit 1)) +
        ZT.natLit 4 * (C * C) * (C + ZT.natLit 1) - ZT.natLit 4 * (C * C) * (C * C + d + ZT.natLit 2))
      ((C - ZT.natLit 1) * (ZT.natLit 4 * (C * C) - ZT.natLit 3 * d * C - d)) := by
  ipra_lc

/-- The `1×1×1×5` prism: `25 R² = 802` and `25 L² = 750 < 802`. -/
theorem prism_example :
    (Γ ⊢[PRAAx] num 25 * num 25 + num 3 * (num 3 * num 3) + num 25 * num 6 ≐ num 802) ∧
    (Γ ⊢[PRAAx] lt (num 25 * (num 25 + num 3 + num 2)) (num 802)) := by
  refine ⟨?_, ?_⟩
  · apply deriveNat; ipra_simps; norm_num
  · show Γ ⊢[PRAAx] le (succ (num 25 * (num 25 + num 3 + num 2))) (num 802)
    ipra_le 51

end LeanProofs.IPRA.Geometry.Hyperbox.ClosedFamilies
