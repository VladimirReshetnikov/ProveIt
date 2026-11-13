# Sparse modular Pell coefficients

`Trace74PellCoefficientReduction.sparse_coefficients` proves, in every
IΣ₁ model, that for positive `m` and the explicit assumptions

```
q*q = m+1,    X ≡ x (mod m),    A = q³*(X+1),
```

the two coefficient residues required by the
[bit-list evaluator](../trace74-pell-bitlist-checker/README.md) satisfy

```
A+1       ≡ q*(x+1)+1                         (mod m)
A*(A+2)   ≡ (x+1)² + 2*q*(x+1)                (mod m).
```

Thus a client can use sparse residues without materializing `X` or the
Pell base, provided it independently establishes the displayed
congruence and parameter bindings. The theorem does not itself compute
a particular power residue or a gcd.

For the candidate, ordinary integer arithmetic gives

```
3056651345 = (2*590069)*2590 + 93925.
```

With `q=2^590069`, `m=q²−1`, and `X=2^3056651345`, this suggests
`x=2^93925`. The decomposition has been checked externally, but the
corresponding model-level power congruence and the concrete coefficient
certificates are **not yet proved by this file**. The sparse expressions
have 683,995 and 683,996 significant bits, respectively, each occupying
85,500 bytes when packed; feasibility of the full Lean kernel check
remains untested.

## Check

The following command exited 0 without warnings on 2026-11-04 with Lean
4.32.0 and previously built dependencies:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-pell-coefficient-reduction Computability/DiophantineConsistency/research/trace74-pell-coefficient-reduction/Trace74PellCoefficientReduction.lean -o /tmp/Trace74PellCoefficientReduction.olean
```

`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
SHA-256:

```
090df1e3589396d59e1b5c646dfbb142220e7398ebd0107c0b50d943a57b72c9  Trace74PellCoefficientReduction.lean
478d822f10dcbf0ec065695e8f683043ff23cfb644f9e0d2318f55178e19e714  Trace74PellCoefficientReduction.olean
6872f8485465666a95dac3de9893c9b102913ae4454f704e1e077c286ea7ada9  Trace74PellBitlistChecker.olean
```

The `/tmp` paths are check-time artifacts, not persistent dependencies.
