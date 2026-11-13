# Compact named formula for the 38-witness Jones expression

This is a **proposed transcription** of the checked endpoint's expression. Its named quantities are macros, not additional unknowns. The exact retained seed is `S = SharingSeed38.seed CurrentWindowCarry2011.ports : Expr (Fin 39)` from the [checked seed source](../nine-sharing-seed38-weighted-retry/src/DiophantineConsistency/SharingSeed38Syntax.lean); it is not the separate quartic compiler seed used in the older nine-variable formula. All nine unknowns `a₀,…,a₈` range over the natural numbers, including zero.

Set `ν=38`, `L=5^39`, and let `Star` be the finite set of `k : Fin 40 → ℕ` with `Σᵣ kᵣ = 4`. For `k ∈ Star`, define fixed integer recipes

```
expo(k) = Σ_{j=0}^{38} k_{j+1} · 5^j
p(k)    = (∏_{j=0}^{39} k_j!) · coeff(expand(S), j ↦ k_{j+1})
z       = 2^(2 + Σ_{k∈Star} |p(k)|)
y       = toNat(Σ_{k∈Star} (z + p(k)) · (2z)^(L - expo(k)))
```

`expand` and `coeff` are the exact executable syntax-coefficient operations in [`SyntaxCoefficients.lean`](../../Lean/DiophantineConsistency/SyntaxCoefficients.lean). The subtraction in each exponent is natural-number subtraction, and `toNat` is the integer-to-natural truncation used in Lean. These recipes are closed and fixed by `S`; no computed literal for `z`, `y` or the coefficients is asserted here.

Use powers and finite sums as symbolic macros and define

```
b = y + 1 + a₀                  B = b^5
q = B^L                          N = q^16
e = Σ_{k∈Star} (z + p(k)) · B^(L - expo(k))
ℓ = Σ_{j=0}^{37} B^(5^(j+1))   λ = Σ_{j=0}^{4L-1} B^j
g = a₁ + 1                      θ = B - 2z
G = 32b · B^(5^38)
```

Let

```
R = (g + e q^3 + ℓ q^5
     + (2(e-zλ)(1+B+g)^4 + λB + λBq^4)q^7)(N^2-N)
  + (q^3-bℓ+ℓ+θλq^3+(B-2)q^8)(N^2-1).
```

Set `h=a₂+1`, `s=a₃+1`, `w=a₄+1`, `φ=a₅`, `i=a₆+1`, `j=a₇+1`, and `t=a₈`. Define

```
U=N²w                 Y=N²s                  M=RY
P=2M²U                K=R+1+h(P-1)           A=M(U+1)
B′=2R+1               W=bw                   C=B′+W+φ
J=4A-5                Q=3WC-2(W²-1)          D=(A²-1)C²+1
E=iJDC²               F=(A²-1)E²+1           G′=A+F(CD+1-A)
H=B′+jC               I=(G′²-1)H²+1
A₀=(P²-1)K²+1         A₁=DFI
V₀=A₀²+2              V₁=A₁²+2
B_d=(JF)²             C_d=(QF+J(H-C))²
D_m=K²G-4(C-KY)²G-8gK²
K_c=B_d(2D_m-1)       T=B_d t+C_d-K_c(C_d+V₀V₁).
```

The proposed final polynomial is

```
(T² + K_c²A₀ - K_c²V₀²A₁)² - 4T²K_c²A₀.
```

All definitions are acyclic and use only fixed integer leaves, nine variables, addition, subtraction, multiplication, nonnegative integer powers and finite sums. This is a compact named formula with high-level sum and power macros, **not** a claimed finite binary-operation DAG, expanded coefficient list, or verified machine-to-Lean serialization. The textual transcription has not yet been independently checked.
