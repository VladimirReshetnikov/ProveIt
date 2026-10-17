# Configurable internal environments and SHIFT

`ValidatorEnvironmentLabels254` gives fixed Sigma1 graphs and total arithmetic
functions for internal free/bound environments and formula encoding. A missing
free-variable entry uses label1. Prepending a label and taking the tail therefore
satisfy their exact lookup laws for every internal index, including out-of-range
indices and the empty vector. Positivity and upper bounds have explicit premises.

The represented encoder uses the HFS state [free,bound,fresh]. At a quantifier
it pushes fresh onto the bound vector and increments fresh by2. Its raw equations
allow arbitrary states and labels; no freshness or semantic correctness is inferred
merely from these computations.

The internal term, vector and formula SHIFT laws are proved by the actual
internal induction APIs. In particular, for every internal UFormula p,

```
encode F B s (shift p) = encode (tail F) B s p.
```

The equality holds through nested quantifiers. It does not rename a CProv proof
or a bundled axiom. Opening a binder, paired-environment alpha equivalence, the
source-proof compiler and encoded ZF axiom clients remain separate obligations.

The source and focused audit passed39 named probes and28 callers, with only
`propext`, `Classical.choice`, `Quot.sound` and zero warnings. Source checking took
15.438seconds and the audit3.050seconds. The first source attempt failed at the
empty-tail projection; adding `pi₂_zero` resolved it without changing limits.
Both attempts and their exact source/driver snapshots are retained.

The runner reuses the checked fixed encoder and its13 ancestors, four direct
external source/object boundaries, and actual Init/Omega providers. All47 proof
inputs are rechecked. The source object is recorded before the audit and checked
unchanged afterward. The available Foundation namespace mirror is not claimed
independently attested in full. Each proof command uses one thread,4GiB, default
options and a120-second bound; prerequisites are neither built nor downloaded.

The portable guard changes only maintained source/audit defaults. Its default
preparation performs no compiler or version call. The root reviewed the source,
audit, guard, repair, and complete successful evidence; no child final proof review
is claimed.

```sh
python Logic/Interpretability/ZFCinPA/check_validator_environment_labels254.py \
  --repo "$PWD" --dependency-root /path/to/pinned/Proofs \
  --output /external/fresh/environment-check
```
