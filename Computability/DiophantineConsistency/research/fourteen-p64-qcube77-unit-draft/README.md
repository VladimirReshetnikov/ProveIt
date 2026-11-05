# 77- and 78-graph positive-zero equivalence

The 77 graph replaces the 78 graph's two first/auxiliary squares and final
`−2` with `(A1*Na−1)²`, retaining the other three squared residuals. The
checked `P64QCube77Existence.same_zero_iff` proves that for every positive
tuple and arbitrary natural ports, the two Lean graphs vanish on exactly the
same tuple in the stated IΣ₁ models. `positive_zero_iff` gives the associated
existence equivalence.

On a 77 zero, the sum of squares forces `A1*Na=1` and transport zero. The
transport bound gives `P≥2`, excluding `A1=−1` by the checked consecutive
Pell theorem. Discrete ordered-ring unit factorization then gives `A1=Na=1`
and the 78 output is zero. Conversely, `P64QCube77OldFacts.residuals` uses
the checked 78 first-residual theorem and arbitrary-first splitter to show its
residual tuple is `(1,0,0,1,0)`, making the 77 output zero.

The three Lean author checks (sessions 82340, 64009 and 47602) each exited 0,
with only `[propext, Classical.choice, Quot.sound]` reports and no warnings or
`sorryAx`. An earlier unit helper check (session 47667) failed on a cast
expression and had an unused-simp warning; both were corrected before the
successful checks. Each successful command used this search path, from the
repository root, with the appropriate source and output module names:

```sh
LEAN_PATH='/tmp/p64-qcube81-ipra-check01:/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib' timeout 180s /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M4000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/fourteen-p64-qcube77-unit-draft Computability/DiophantineConsistency/research/fourteen-p64-qcube77-unit-draft/P64QCube77Existence.lean -o /tmp/P64QCube77Existence.olean
```

Hashes were recorded after the checks. The author checks use captured
providers; they are not a guarded before/after replay or complete transitive
source-to-object rebuild. The iPRA endpoint and file/display identification
are separate.

| File | SHA-256 |
| --- | --- |
| `P64QCube77Unit.lean` | `73e76eaa00bfcae01fa2b13a83892547c44c4aba34f58af4185920cfafe871dd` |
| `P64QCube77OldFacts.lean` | `d100eb7a6f573fbe042657f52c1de36551ad48a09a3679dc9a65209f80be60da` |
| `P64QCube77Existence.lean` | `e65822241f4308d969094f91b68a90a5c267ad82b852b3b7b68f2fad769a942a` |
| `/tmp/P64QCube77Unit.olean` | `5e4e354b5a0a420c94967ca71c99a5088d41bac615651225c5aaf44a9390370d` |
| `/tmp/P64QCube77OldFacts.olean` | `48b2c4d8dc7a4a3b56123a519f0989ef0d48b35f9ecfb28be5d56f17c65003fd` |
| `/tmp/P64QCube77Existence.olean` | `0cd0fa8b52a8cad49bad9db49507f16acb0171ee56dad0e21783515facf15a72` |
| `/tmp/P64QCube77Binding.olean` | `550873ad2b0074bfb3265c1f828957b697787806cf367383ecf7d6d8b8275c3d` |
| `/tmp/P64QCube78GraphSplit.olean` | `76da5f69b14d211994c5ccc12e9e9de9d5d3b585b002149bca4922d7ca536150` |
| `/tmp/P64QCube78Existence.olean` | `8371368a8feb9de7e729501224455ab26848c1509b88c93aadd757b38e0bd669` |
