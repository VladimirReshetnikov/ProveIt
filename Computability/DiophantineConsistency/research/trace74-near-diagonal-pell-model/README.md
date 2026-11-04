# Model-indexed power gap from the 74-operation Pell gap

`Trace74NearDiagonalPellModel.lean` proves in Lean, for arbitrary elements of any model of `IΣ₁`, that

```text
(2Y) y_(n+1)(2(XY²−1)+1) < y_(r+1)(Y(X+1)−1)
    ⇒ (2Y) power(X(2Y)²,n) < power(2X(2Y),r),
```

assuming `X ≥ 2` and `Y ≥ 1`. Here `y` is the repository's paired Pell ordinate, parameterized by half its recurrence coefficient minus two, and `power` is the represented variable-base exponentiation on the model, not Lean's natural-number exponent. The proof instantiates the existing represented-induction Pell sandwich, comparing its two bases to the displayed bases. Indices in this lemma are one less than the indices denoted `n,r` in the ordinary-integer near-diagonal note.

This is a conditional numerical inequality only. In particular it does not derive the Pell gap or bind it to a graph valuation, derive the additional near-diagonal index window, finish the height estimate, settle the reverse guard, or prove an iPRA endpoint.

An author check invoked Lean with a 120-second timeout and a 3 GB Lean memory limit:

```text
LEAN_PATH=/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-near-diagonal-pell-model \
  Computability/DiophantineConsistency/research/trace74-near-diagonal-pell-model/Trace74NearDiagonalPellModel.lean \
  -o /tmp/Trace74NearDiagonalPellModel.olean
```

The process exited zero. Both theorem axiom reports were `[propext, Classical.choice, Quot.sound]`. SHA-256: source `b992782b59afe878a425cbe29f9194ee31c5e713050dee9f3e6e7eb83517a892`, output object `af9a5f302648ea6bab75b3bb62c8ba74e48c3922f68b0af30364b22991d621bb`, Lean executable `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; the direct imported provider objects for `ArithmeticHalfBinomialSandwich` and `ModelDifferenceRing` had hashes `34a402c9371d3c1a0917a401135e2bcdce68184b578699ebd267c115473c2b7e` and `d0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74`. These temporary provider paths, their transitive dependencies and search-path resolution have not been independently audited here. The command is a captured-provider author check, not a clean current-source rebuild.
