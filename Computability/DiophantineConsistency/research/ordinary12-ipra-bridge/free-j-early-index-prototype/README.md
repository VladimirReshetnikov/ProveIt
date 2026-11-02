# Free-J early first-index bound

For the exact free-J graph in an `IΣ₁` model, Lean combines the first/main Pell
index existence, q³ divisibility, signed q⁴ congruence and early scalar window.
From an internal zero, positive coordinates and β, and explicit model bounds
`MC < β` and `MF < 2β`, it constructs a first Pell index `n ≥ 13` with
`2n ≡ R+1 (mod q⁴)` and `R+1 ≤ 2n` and `R+1 ≤ k`. The four ports are arbitrary
naturals subject to those assumptions. It uses no strong norm, later rank,
fixed-port interpretation or checker calibration.

Fresh historical replay session 12927 actually exited 0 and printed
`PASS_BOUNDED_FREEJ_EARLY_INDEX
339cf9765bc34dc549c084e9881d7732ac9e95d2ae5fba4d17ecbf295dbcc77d`.
The replay rebuilds both the Pell-index and early-window dependencies against
one coherent historical provider and preserves their ancestry. The original
warning-bearing exploratory source and observation are under `observations/`.
This is single-author model evidence, not a matched full-project replay, a
dynamic dependency audit, an index-comparison proof, or an iPRA derivation.
