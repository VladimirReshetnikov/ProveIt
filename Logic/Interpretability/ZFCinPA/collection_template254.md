# A fixed Collection proof from three schema instances

`CollectionResources254` and `CollectionTemplate254` prove one ordinary
extended-language Collection sentence. The source theory consists of lifted
ordinary ZF, equality for the enlarged language, and exactly three individual
predicate-dependent schema sentences. This supplies a fixed standard proof
that a later model-coded compiler can translate; it does not yet provide an
internal proof of the numerical G clause or a PA consistency comparison.

The language is `setTemplateLanguage 1 (fun _ => 2)`, with a binary predicate
`R` whose input is argument 0 and output is argument 1. The conclusion is

```
forall A exists B.
  (forall x in A forall y. R(x,y) -> exists z. R(x,z) and z in B)
  and (forall y in B exists x. R(x,y)).
```

## Why three schemas suffice

Write `W(x,c)` for the assertion that the rank stage `V_c` contains some
`R`-output of `x`. A least witness rank satisfies

```
L(x,c) := Ord(c) and W(x,c)
          and forall e. Ord(e) -> W(x,e) -> (c=e or c in e).
```

Use the globally total relation

```
T(x,c) := L(x,c) or ((not exists y. R(x,y)) and Empty(c)).
```

Witness-rank Separation and Regularity yield a least rank whenever an output
exists. Pure ordinal comparison proves uniqueness. When no output exists,
the empty ordinal is the unique fallback. Every `T`-value is an ordinal.
Replacement applied directly to the original set `A` therefore gives a set
of ordinals `I`; its union bounds a rank stage containing an output for each
input that has an output. Output Separation cuts the desired image subset
from that stage.

The three explicit resources are witness-rank Separation, total-rank
Replacement, and output Separation. This avoids domain Separation and
image-carving Separation in the literal partial-Replacement route. Pure
rank/ordinal lemmas use ZF schemas only for predicates in the original set
language. No arbitrary-`R` Separation, partial Replacement, class choice,
or external well-foundedness is added silently. Enlarged-language equality
explicitly contains binary `R` congruence; no minimality claim about equality
is made.

The syntax module constructs the three matrices and their actual `.univCl`
schema sentences, identifies their semantics, and applies ordinary
first-order completeness to the one fixed source sentence. Its named syntax
handles arbitrary environments. This use of ordinary completeness selects
one standard finite source proof, not an internal model's proof or an
internal source-derivation compiler.

## Checked scope and provenance

The successful record is `results/collection-template254-verification.json`.
Both sources and the focused audit passed Lean 4.32.0: 7 ordered axiom reports,
12 callers, only `propext`, `Classical.choice`, and `Quot.sound`, zero warnings.
Resources took 0.418 s, the syntax/template module 3.199 s, and the audit
1.507 s. All 67 input hashes, actual first providers, dependency state, and
both fresh objects matched after the audit.

The checker selects exactly 18 existing project objects: NativeZF's fresh
object and ten native ancestors, plus the two freshly checked unchanged
OpenSet precursors and five syntax ancestors. The OpenSet and Buffered
client objects are not imported. The six external boundaries include four
actual imports and two explicitly identified dependency-discovery anchors;
Init, Std, Lean, and Omega first providers are checked separately. Cached
Foundation boundaries are pinned source/object boundaries, not an assertion
that the whole transitive namespace was rebuilt. No Cantor, decoder, or
SetCongruence project object enters this closure. The OpenSet parent record
honestly retains its two inherited warnings; the two new modules and audit
have none.

All six attempts are preserved in `results/collection-template254-history.json`.
Run 2 was explicitly interrupted by SIGTERM on the parent's compiler queue
request; it is not a completed proof check. Runs 1, 3, 4, and 5 failed. Only
run 6 passed both modules and the audit. The history includes exact source,
audit, guard, diagnostics, earlier unbuilt preparations, and repair deltas.
No limits or dependencies were increased. The portable guard differs from
the executed guard only by deleting unused historical scratch-path metadata.

## Reproduction

With the pinned dependency checkout and the recorded cached objects present,
from the repository root run

```sh
python Logic/Interpretability/ZFCinPA/check_collection_template254.py \
  --repo "$PWD" --dependency-root /path/to/pinned/Proofs \
  --output /external/fresh-output
```

`--prepare-only` checks identities and providers without a proof build; it
still queries `lean --version`. Sources, audit, exact native/OpenSet evidence,
compiler, library paths, project cache, and namespace cache have explicit
flags for relocation. Defaults resolve maintained source/audit/evidence
paths. The checker never builds dependencies or downloads providers and
requires a fresh external output directory. Proof builds use 4 GiB and one
Lean thread, with ordinary default heartbeat limits.

## Remaining internal client

For each buffered interpretation of `R`, the compiler still needs actual
target proofs of the translated three schema sentences and enlarged equality.
The checked open-schema proof constructors and existing SetCongruence source
APIs are relevant resources; this packet does not check or discharge that
whole callback family. The translated Collection conclusion must then be
matched with the exact numerical G syntax, retaining both gates and handling
coincident labels, the positive own-code freshness result, and decoded zero's
literal truth formula with free label 0. No bundle, all-accepted-proof,
ZFC proof-code, binary simulation, PA endpoint, or state-count claim follows
from this checkpoint alone.
