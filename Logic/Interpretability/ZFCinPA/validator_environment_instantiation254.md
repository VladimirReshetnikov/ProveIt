# Internal source instantiation for the configurable encoder

`ValidatorEnvironmentInstantiation254` proves the exact encoding identity for
substituting an arbitrary internally typed set-language term into the sole
bound slot of a source formula:

```text
E(F,[],s,substs1(t,p)) = E(F,[termLabel(F,[],t)],s,p).
```

The theorem `encode_substs1` assumes `IsSemiformula ℒset 1 p` and
`IsTerm ℒset t`. The free-label environment `F` stays fixed. In the fixed
set language there are no function symbols, and a term at bound depth zero
cannot contain a bound variable. Thus every internally typed term is a free
variable, and its interpretation is the actual `freeLabel(F,index)`, including
fallback label 1 when the index is outside the stored environment.

The generalized identity works at every internal bound depth `d`. The
represented substitution vector is `qVecIter d [freeVar(index)]`: it preserves
the lower bound slots and replaces slot `d` by the selected free variable.
The explicit environment condition is

```text
Ext(d,B,B',x) :=
  len(B)=d ∧ len(B')=d+1 ∧
  (∀ i<d, B'[i]=B[i]) ∧ B'[d]=x.
```

With `x=freeLabel(F,index)`, `encode_instantiateAt` proves

```text
E(F,B,s,instantiateAt(d,index,p)) = E(F,B',s,p).
```

Under either quantifier both sides prepend the same allocated label, advance
the next binder label by 2, and use the checked `ext_cons` law. The proof covers
internal terms, term vectors and every internal well-formed source formula.
It uses Π1 structural induction in IΣ1 and the existing fixed Δ1 graphs for
substitution, vector iteration, lengths and encoding. There is no external
natural-number recursion over represented syntax.

This reuses the [opening module](validator_environment_opening254.md) and
[configurable environment encoder](validator_environment_labels254.md).
Opening first shifts the source free indices and extends the free environment;
this instantiation identity keeps the free environment fixed. No positivity,
injectivity or binder-stream avoidance premise is required for these literal
syntax equalities. A later existential proof-rule transport must supply the
logical resources it uses; the identity alone does not prove that rule.
Source-derivation compilation, axiom transport and the reverse consistency
endpoint remain separate. No machine-state reduction is claimed here.

## Verification

The 190-line source and 70-line audit passed their first pinned Lean 4.32.0
check: **12 named axiom reports and 16 explicit callers**, using only
`propext`, `Classical.choice` and `Quot.sound`. The source has no warnings.
The audit retains one unused-variable warning for `hB` in its bottom-code
client. Successful source/audit bytes are preserved exactly, with no cosmetic
recompilation.

The source took 27.186 seconds and the audit 2.353 seconds, with one thread,
4 GiB, default proof limits and a 120-second timeout per command. The source
object hash was saved before the audit and checked afterward. The
[exact PASS record](results/validator-environment-instantiation254-verification.json)
is retained unchanged.

The guard reuses the exact checked Opening parent and its actual closure:
24 project modules, six direct external boundaries and two toolchain
providers. It checks 71 current input paths and the actual first provider
for every selected module. There is no additional external boundary or new
choice among same-source Cantor objects. Existing external cache identities
are explicit boundaries, not an attestation of an entire Foundation namespace.
No dependency was built or downloaded.

The [history](results/validator-environment-instantiation254-history.json)
preserves the exact successful source, audit, executed guard and logs, the
initial unbuilt preparation, and the separate maintained-default preparation.
The portable guard changes only maintained source/audit defaults. The
[reviews](results/validator-environment-instantiation254-review.json) distinguish
the earlier source-only review from review of the actual successful evidence.
Maintained-default preparation is unbuilt and makes no proof compilation or
compiler-version query.

## Reproduction

From the repository root, with the existing checked prerequisite objects:

```sh
python -B Logic/Interpretability/ZFCinPA/check_validator_environment_instantiation254.py \
  --dependency-root /path/to/dependency-checkout \
  --output /fresh/external/environment-instantiation
```

`--opening-evidence` accepts a relocated copy of the exact parent record.
`--project-cache` may select a supplied cache containing the 24 prerequisite
project objects, and `--namespace-cache` a cache root containing the Foundation
namespace mirror. `--source` and `--audit` accept relocated copies of the frozen
successful bytes. `--prepare-only` performs no proof compilation or
compiler-version query.
