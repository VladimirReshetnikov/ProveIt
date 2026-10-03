# Independent review: Compressed Queue Diophantine Research

Reviewed archive `Compressed_Queue_Diophantine_Research.zip`, SHA256 `cd3cfe40497cca4a3b4781a25b37405f5452e0dae26b70163245d80b53ad0a20`. All 13 member hashes/sizes matched the intake manifest before safe private extraction. Read the complete article, README/provenance, compiler, verifier, and independent JSON checker. This is an ordinary mathematical/source review with finite regression evidence, not proof-assistant verification.

## Findings and repair

No theorem-level defect found in the finite endpoint, resource composition, first-failure/repetition, Fine–Wilf/conjugacy, ordinary infinite-loop quartic, or explicitly exponential powered-grammar arguments.

**P2, low-level exactness boundary:** `code/queue_certificates.py:132` accepts noninteger coefficients through `Poly(terms)`, despite documenting a sparse integer polynomial and enforcing exact integers in `coerce`. For `Poly({(): float(2**60), (0,): -1.0})`, the natural witness `2**60+1` gives floating residual `0.0`; a directly constructed `Certificate` accepts, although the exact intended residual is −1. The high-level compiler itself emits integer coefficients, and the separate export checker rejects float coefficients. This finding therefore affects the public low-level constructor contract, not the compiler theorem.

**P3, action input boundary:** `Action(read=['0'], write='0')` is accepted. Its nominally frozen object retains the caller's mutable list. Compiling the one-action trace at input/output `'0'` yields a zero; changing the list to `['1']` changes the current action so a fresh compilation rejects, while the old certificate stays zero. The direct operational runner also expects a string. Rejecting nonstring words restores the documented word API.

The separate `compressed_queue_exact_inputs.patch` requires exact string action words/alphabets, exact integer control labels, exact `Action` leaves and natural grammar indices, and exact integer coefficients with sorted natural-index monomials. It snapshots the coefficient dictionary as before. It is an input-contract repair, not a new theorem. Arbitrary reassignment of public Python fields is outside this constructor guarantee.

Patch SHA256: `ed4aa5503033bb2c89dbe16eccdef62ad16101014c7c5c080d6c6f8d77a33501`; original compiler `d5fbf10fdaa26818f6ca0c925cf2c6d10e59a633b74fd465cb370a6ed035fbe6`; privately patched compiler `bfebd20d42a1d6921d29c36b98e397115343502f7235e2e5a4ae756908a6fa74`. No archive was modified.

## Mathematical scope and arithmetic accounting

The externally supplied acyclic grammar determines the entire ordered transition trace, including control composition. The endpoint theorem needs both the word identity `qV=Ur` and the resource inequality `|q|≥R`; the resource condition prevents reading symbols supplied only by later appends. The chronological read-before-write convention is consistently maintained. All witness variables are natural including zero. Fixed leaf words force actual encodings; arbitrary numeric word pairs are not silently assumed to decode.

For `l` leaves and `c` concatenations (`g=l+c`), the original finite compiler has `6g+3c+1` coordinates and `6l+9c+3` quadratic residuals. Every coordinate is uniquely determined for a true fixed endpoint instance, including unused grammar nodes. Its sum of squares has degree at most four. The infinite closed-macro compiler pays binary word-power chains for fixed exponents and likewise has a unique natural fiber. Its `a=0` and shrinking `b<a` cases legitimately reduce to constants zero and one. The separate powered-grammar theorem retains explicit exponentiation predicates; the emitted ordinary quartic exporter does not implement variable exponentiation.

The claims concern compressed supplied traces or supplied periodic lassos. The grammar size remains external, may be arbitrarily large, and is not bounded computably over universal accepting computations. Periodic lassos do not characterize all divergence. The 17-node doubling example represents 65,536 steps using 151 coordinates, but its scale already has 103,873 bits. Sparse unexpanded arithmetic size, trace length, and binary integer complexity are distinct. There is no fully instantiated fixed-arity universal equation or improvement of the current universal arithmetic ledger.

The literature framing is supported by primary sources: [Huschenbett–Kuske–Zetzsche's queue action monoid paper](https://arxiv.org/abs/1404.5479) addresses the queue-action algebra, while [Köcher's reliable queue reachability paper](https://link.springer.com/article/10.1007/s00224-021-10031-2) explicitly discusses Turing-complete reliable queues and earlier loop-acceleration work. The report does not establish a novelty priority claim. The fully compressed word-algorithm corollary relies on an external algorithm, not the complexity of the provided large-integer evaluator.

## A sound finite-family projection

The review helper includes an actual sparse-polynomial projection of the finite compiler, with **`6c+1` natural coordinates and `6c+3` quadratic residuals**, hence degree at most four. This is a witness/residual improvement for the externally supplied grammar family, with no unmeasured arithmetic-gate improvement asserted.

Replace all six leaf coordinates by their constants. For an internal node retain four word coordinates and `α,β`, define its resource values recursively by `R=R_left+β`, `S=S_right+α`, and restore the old cancellation variable as `d=S_left−α`. Retain the four word rows and replace the three min rows by

`R_right−S_left+α−β=0`, `αβ=0`.

These two equations on natural `α,β` force the unique complementarity solution. If `α=0`, then `d=S_left≥0`; otherwise `β=0` and `d=R_right≥0`. All restored resources are nonnegative affine expressions. Thus the projection and restoration are inverse on natural zeros, with no uncharged inequality. The root retains its slack and all three boundary rows.

Substituting the restoration expressions into the full original sum of squares gives the new sum of squares identically on every integer tuple: omitted leaf/resource/first-min residuals become the zero polynomial. Naturality of the restored cancellation values is asserted only at new natural zeros. Affine resource expansion can increase sparse size, so this is not claimed to preserve the original linear sparse-monomial bound or to reduce arithmetic operations. The helper tests actual emitted polynomials and checks that all omitted residuals vanish symbolically.

## Portable replay and evidence

`review_compressed_queue_aebfa.py` authenticates article/compiler/checker/verifier and the patch before importing or applying them, rejects `python -O`, copies the package privately, and applies the patch using `patch --batch --fuzz=0`. No fixed `/tmp` paths are required:

```sh
python review_compressed_queue_aebfa.py \
  --root /path/to/untouched/Compressed_Queue_Diophantine \
  --patch compressed_queue_exact_inputs.patch --authors \
  --output /path/to/new-receipt.json --expect review_compressed_queue_aebfa.json
```

The original author commands, run on both private original and repaired copies, are:

```sh
python code/verify.py
python code/check_certificate.py data/example_quartic.json data/infinite_growth_quartic.json
```

All **259,025 author checks** passed on both copies. All saved receipt fields reproduce exactly after dropping only the interpreter-version field; both example certificate exports are byte-identical to the archive and to each other. The independent review completed **1,425 assertions**, including 160 actual projected compiler cases, 320 complete signed/natural graph identities, 64 exhaustive small complementarity fibers, 294 directly simulated loop cases, 73 false-witness mutations, 18 malformed-input rejections, and exact compiler output preservation. These finite checks supplement the general proofs and do not enumerate all witnesses or all universal programs.
