# Opening an internal binder in the configurable encoder

`ValidatorEnvironmentOpening254` proves the exact term, vector and formula
identity needed to encode the opened matrix in Foundation's universal rule.
The source depth, syntax and variable environments are arbitrary elements of an
IΣ1 model, including nonstandard ones. This advances the reverse internal
proof compiler after the checked [environment and SHIFT computation](validator_environment_labels254.md).

Write `E(F,B,s,p)` for the configurable numeric formula encoder. `F` stores free
variable labels, `B` stores bound variable labels, and `s` is the next binder
label. The explicit extension relation is

```text
Ext(d,B,B',x) := len(B)=d ∧ len(B')=d+1 ∧
                 (∀ i<d, B'[i]=B[i]) ∧ B'[d]=x.
```

Thus the shorter stack retains every lower slot, and the longer stack has the
distinguished label `x` at its final slot. For every internally well-formed
source formula `p` of depth `d+1`, the checked theorem is

```text
E(x::F,B,s, subst(qVecIter d [&0], shift(p))) = E(F,B',s,p)
```

under `Ext(d,B,B',x)`. The same equality is proved for source terms and their
argument vectors. SHIFT increments each source free index; the extra label at
the head of `F` restores its previous interpretation. The iterated substitution
vector retains each protected bound slot and opens its final slot to free `&0`.
The iterator and this vector specification come from the checked
[internal specialization construction](model_coded_specialization.md).

The formula proof uses internal Π1 structural induction. Under a quantifier,
it pushes the same binder label `s` onto both bound environments and changes the
next label to `s+2`. The extension relation is preserved, while the existing
`qVecIter_succ` equation identifies the substitution under that binder. It uses
no recursion over external natural numbers or finite table of source indices.

At depth zero the main theorem becomes

```text
E(x::F,[],s,free(p)) = E(F,[x],s,p).
```

Two finite clients identify the actual encoded universal and existential
matrices. For instance, universal introduction now has the exact computation

```text
E(F,[],x,ALL(p)) = wal(x, E(x::F,[],x+2,free(p))).
```

The identity holds for arbitrary labels, including zero. Freshness and reserved
labels are separate proof obligations. This checkpoint supplies no CProv alpha
conversion or source derivation translation. In particular, the shifted source
contexts still need alpha equivalence when their encoder's next binder label
changes. No ZF axiom transport, consistency comparison, PA endpoint or new
machine-state bound is claimed here.

## Verification

The 203-line source and focused audit pass pinned Lean 4.32.0 with **19 named
axiom reports, 22 callers, the standard three axioms only, and zero warnings**.
The source check took 24.362 seconds and the audit 2.690 seconds, using one
thread, 4 GiB and default Lean limits, with a 120-second timeout per command.
The source object hash was persisted before the audit and remained unchanged.
The [exact successful record](results/validator-environment-opening254-verification.json)
is retained without modification.

The checker reuses the exact checked environment and specialization parents,
23 project objects and six direct external boundaries. It checks 70 current
input paths, their before/after equality and their actual first providers. The
Cantor object is the environment lane's existing object. The two additional
boundaries relative to that lane are Foundation's typed proof syntax and
`InductionSchemeDelta1`, inherited from the specialization closure. These are
cached boundaries; no entire Foundation namespace attestation is asserted.
No dependency was built or downloaded.

The first source attempt failed on two elaboration details: simplification did
not unfold the explicit set-language function recognizer, and the depth-zero
caller needed to normalize `0+1`. The second attempt passes after those two
local repairs, with the same theorem statements and audit. Exact failed and
successful sources, drivers, records, logs and preparatory records remain in
[the history](results/validator-environment-opening254-history.json). The portable
runner differs from the executed runner only in maintained source/audit defaults.
The [author and independent reviews](results/validator-environment-opening254-review.json)
record current hashes, first-provider checks and the separate unbuilt default preflight.

## Reproduction

From the repository root, with the existing checked prerequisite objects:

```sh
python -B Logic/Interpretability/ZFCinPA/check_validator_environment_opening254.py \
  --dependency-root /path/to/dependency-checkout \
  --output /fresh/external/opening
```

`--environment-evidence` and `--specialization-evidence` accept relocated copies
of the exact recorded parent evidence. `--project-cache` may select a supplied
cache containing all 23 prerequisite project objects; `--namespace-cache` may
select a cache root containing the Foundation namespace mirror. `--source` and
`--audit` accept relocated copies of the frozen successful bytes.
`--prepare-only` performs no proof compilation or compiler-version query.
