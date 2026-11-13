# Symbolic nine-variable formula from the 33-witness seed

This is a proposed human transcription of the independently checked Lean named formula. Its named quantities are abbreviations, not extra unknowns. The nine unknowns `a₀,…,a₈` range over the natural numbers, including zero; names are case-sensitive. The exact symbolic seed is `S = SharingSeed33.seed CurrentWindowCarry2011.ports : Expr (Fin 34)` in [the checked seed source](../nine-sharing-sign33-seed-syntax-check/src/DiophantineConsistency/SharingSeed33Syntax.lean). The checked [named Lean identity](../nine-sharing-sign33-jones-named-formula-check/src/DiophantineConsistency/Sign33NamedFormula.lean) and [symbolic iPRA endpoint](../nine-sharing-sign33-ipra-endpoint-check/src/DiophantineConsistency/Sign33IPRAEndpoint.lean) do not read this document. Independent review of this transcription is required.

Set `L = 5^34`, and let `Star` be the set of vectors `k : Fin 35 → ℕ` whose coordinates sum to 4. Define these fixed recipes from `S`:

```text
expo(k) = Σ_{r=0}^{33} k_{r+1} · 5^r
p(k)    = (∏_{r=0}^{34} k_r!) · coeff(expand(S), r ↦ k_{r+1})
z       = 2^(2 + Σ_{k∈Star} |p(k)|)
y       = toNat(Σ_{k∈Star} (z + p(k)) · (2z)^(L - expo(k)))
```

`expand` and `coeff` are the syntax-coefficient operations in [SyntaxCoefficients.lean](../../Lean/DiophantineConsistency/SyntaxCoefficients.lean). Subtraction in exponents is natural-number subtraction; `toNat` is the integer-to-natural truncation from Lean. These are closed symbolic definitions, not newly computed decimal literals.

Use powers and finite sums as symbolic abbreviations:

```text
b = y + 1 + a₀                  B = b^5
q = B^L                          N = q^16
e = Σ_{k∈Star} (z + p(k)) · B^(L - expo(k))
ℓ = Σ_{r=0}^{32} B^(5^(r+1))   λ = Σ_{r=0}^{4L-1} B^r
g = a₁ + 1                      θ = B - 2z
G = 32b · B^(5^33)
```

Let

```text
R = (g + e q^3 + ℓ q^5
     + (2(e-zλ)(1+B+g)^4 + λB + λBq^4)q^7)(N^2-N)
  + (q^3-bℓ+ℓ+θλq^3+(B-2)q^8)(N^2-1).
```

Set `h=a₂+1`, `s=a₃+1`, `w=a₄+1`, `φ=a₅`, `u=a₆+1`, `v=a₇+1`, and `t=a₈`. Define

```text
U=N²w                 Y=N²s                  M=RY
P=2M²U                K=R+1+h(P-1)           A=M(U+1)
B′=2R+1               W=bw                   C=B′+W+φ
J=4A-5                Q=3WC-2(W²-1)          D=(A²-1)C²+1
E=uJDC²               F=(A²-1)E²+1           G′=A+F(CD+1-A)
H=B′+vC               I=(G′²-1)H²+1
A₀=(P²-1)K²+1         A₁=DFI
V₀=A₀²+2              V₁=A₁²+2
B_d=(JF)²             C_d=(QF+J(H-C))²
D_m=K²G-4(C-KY)²G-8gK²
K_c=B_d(2D_m-1)       T=B_d t+C_d-K_c(C_d+V₀V₁).
```

The proposed equation is

```text
(T² + K_c²A₀ - K_c²V₀²A₁)² - 4T²K_c²A₀ = 0.
```

This is a compact symbolic presentation, not an expanded coefficient list or a finite binary-operation count. The [external macro-DAG prototype](../nine-seed33-jones-compact-macro-prototype/) has 45 live named nodes, which is not an arithmetic-operation count; its JSON-to-Lean semantic binding remains unproved. The separately audited [external degree survey](../nine-seed33-jones-metric-survey/) gives a conservative candidate upper bound, not an exact degree or a Lean degree theorem. No numerical export or direct PDF binding is asserted.
