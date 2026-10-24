# A direct quartic in 508 unrestricted integers

The main equation is the literal ordinary integer polynomial

`P(z_1,...,z_508) = sum_{j=1}^{308} R_j(z)^2`.

The complete quadratic residuals are in `equation.json`; their complete
collected expansion is in `expanded_polynomial.json`. The LaTeX file
`residuals508.tex` prints every residual, using one-based display indices.
JSON coordinates are zero-based. All coefficients are ordinary literal
integers. Named factorial, binomial, and power functions are only semantic
descriptions in the proof; none is an operation in the final polynomial.

## Result and comparison

| Construction | Integer variables | Quadratic residuals | Degree | Monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Incoming Round 14 matched parent | 517 | 310 | 4 | 6,774 | 3,904,267 |
| Complete cofinal checkpoint | 512 | 310 | 4 | 6,742 | 3,904,268 |
| Consecutive-product modulus | **508** | **308** | **4** | **6,545** | **996,521** |

The new equation improves all four varying metrics over the matched
517-variable parent in the direct C222 proof-calculus route. The incoming
519-variable alternative still has fewer terms and lower coefficient
height: 6,253 terms and height 411,060. No global minimality is claimed.

Together with the explicitly inherited ordinary C222/ZF/ZFC calibration,
the ordinary proof establishes that ZFC proves the absence of integer
zeros equivalent to syntactic `Con(ZFC)`. It does not prove the absence
of zeros or assert a new Lean/Rocq derivation. This construction neither
encodes a K215 run nor uses Jones's universal polynomial.

## The structural change

The proof horizon is restricted to the cofinal family `t=16+s^2`.
The factorial output `F` is initially an arbitrary integer. An already
present square wire represents `F^2`. The new source uses

```
rho = F^2*t^2
V = (rho+1)^t
R = 2+t+x+y+F^2
K = 2R
y = V(V-1)
```

The power line describes the already represented power request; its
implementation is the literal quadratic Pell system. The other new
lines are quadratic in existing coordinates and require no extra square
wire for V.

For every integer V, the product V(V-1) is nonnegative. Hence y+1 is
positive before any indexed-Pell semantics, with no sign premise on
F or V and no exceptional-zero argument. The actual q^t request then
orients the main pair, giving V positive. The raw factorial ceiling
forces F positive. The squared-radius factorial lemma identifies it
as t!, while the removed endpoint sign follows from V>=F+2.

Completeness uses the proof's actual resource bound. Each pending product
S contains at most t+1 factors of size at most Ft+1. The strengthened
bound `S<V=(F^2*t^2+1)^t` follows from elementary inequalities given in
`PROOF.md`. Canonically V is one modulo F and at least three. Thus
the fixed y=V(V-1) is a multiple of F, exceeds every pending product,
and satisfies y>=F+1. Fresh beta-CRT and downstream witnesses exist.

`PROOF.md` gives both directions and the required noncircular order of
the arithmetic arguments. `COFINAL_PROOF.md` retains the independently
complete 512-variable checkpoint and its general cofinal specialization
lemma. `VARIANT_COMPARISON.json` records the final small modulus search;
the packet contains only the selected polynomial's full coefficient data.

## Reproduce and verify

Only Python's standard library is needed. From this directory:

```
python3 verify.py --output verification-local.json
python3 -O verify.py --output verification-optimized-local.json
python3 build.py --output /tmp/conzfc508-consecutive-regenerated
```

The builder uses explicitly bundled frozen parent modules. It performs
the signed source specialization, exact Horn factorization, integral monic
projection, and integral coordinate translation before collecting every
coefficient. It writes only to the requested output directory.

The independent `verify.py` imports none of those producer modules. It
checks every altered source row and coordinate, independently reconstructs
the Horn factorization, verifies all 222 integral restorations and the
two unconstrained coordinates, verifies 13 coordinate translations in both
directions, and recomputes every coefficient. It also recomputes the
41-atom square frame, all 16 actual seed bounds, and the exact identity
`(2V-1)^2=4y+1`. Four raw norm/residue cuts remain checked diagnostics;
they are not used to establish the initial sign of y. Negative controls
reject corrupted source and coefficient data. These finite artifact
checks accompany the separate ordinary proof of the unbounded theorem.

`VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, and `REPRODUCTION.json`
record completed checks, including byte-identical regeneration of all 11
builder outputs. `SEED_AND_BOOTSTRAP_CERTIFICATE.json` records the actual
seed, frame, square-identity, and diagnostic bindings.
`source_transformation.json`, `factorization.json`, `projection2.json`,
and `translation.json` retain the exact maps.

## Source and credit

The source is Vladimir Reshetnikov's ProveIt repository at commit
`45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`, specifically the incoming archive
`ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.zip`.
`PROVENANCE.json` records exact source hashes. Selected unchanged parent
proofs, source graphs, maps, and tools are bundled under `parent/`.
`source517.json` is the byte-identical final 517-variable comparison.

This research and its proof/audit code were developed with AI assistance.
The new claims are the cofinal source restriction, signed factorial
recovery with a squared radius, deterministic consecutive-product modulus,
their complete soundness/completeness argument, and the checked 508-variable
specialization. The proof-calculus calibration and retained uniform Pell
and CRT machinery are inherited and credited accordingly.
