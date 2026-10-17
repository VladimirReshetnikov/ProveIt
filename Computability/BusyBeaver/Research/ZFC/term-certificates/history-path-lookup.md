# First prototype: path witnesses with linear template lookup

This records the first experimental transformation of source50's exact ground-term certificate checker. It removes the checker's global constructor-key uniqueness requirement. Two bundle freshness gates instead carry finite paths witnessing that their normal ground terms differ. It preserves all 12 source50 rule templates and the fixed falsity target `F=B1(Z,Z)`. The ordinary argument below establishes the intended soundness/completeness of this transformation; the Python tests are finite QA, not a formal proof or a Turing-machine state measurement.

Source50 is the archived manuscript *Canonical term certificates for small consistency machines*, received in commit `85633fd2f57b5dca16f87667699134d1b500ebc0` after current commit `82a41caaccd61b7900a4691354d7b457928a8b61`. Its own historical source pin is `fab89c5d26b81cd2ccab2ee5d213ff23725c7726`. The replayed prototype imports recovered source50 fixed templates from `source50/code/symbolic254.py` and `source50/data/spec254.json`. The test producer additionally uses copied `canonical254.py`, `term254.py` and `check_term254.py`. No delivered file is edited, no submitted suite is repeated, and no checksum-manifest check is run. The identities recorded in `results.json` identify the files used by this new experiment.

## Representation and the removed obligation

An arena starts with the sole zero node `0:Z`. Each later node is `Btag(left,right)`, with tag in 0..3 and strictly earlier child indices. The one forbidden constructor is `B0(0,0)`. Every other positive node is permitted, including repeated identical keys and distinct keys whose recursively unfolded terms coincide. The represented natural value is

`value(Z)=0`, `value(Btag(x,y))=4*P(value(x),value(y))+tag`,

where `P(a,b)=(a+b)(a+b+1)/2+b` is the exact C254 Cantor orientation. This is a mathematical denotation; the checker does not compute it.

Topological order makes every value well-defined. By induction the sole zero-valued node is node 0: a positive tag gives a positive value, and a tag 0 node has at least one nonzero-valued child because its literal zero/zero key is forbidden. Thus it too has positive value. Reduction modulo4 distinguishes tags. For equal tags, Cantor injectivity identifies both child values. Consequently two unfolded normal terms have equal values exactly when their constructor trees agree. Duplicate positive nodes can represent the same value, so ID inequality is no longer a sound freshness test. ID equality remains a sufficient test of value equality.

`validate_nodes` uses one forward pass and no set, dictionary, pairwise uniqueness comparison or structural equality recursion. It checks only local node shape, tags, backward references and the sole zero alias. The statistic `arena_uniqueness_comparisons=0` describes this explicit absence; it is not an independently proved runtime complexity bound.

## A small exact disequality witness

A witness is a finite list of left/right bits. Starting at the two parameter roots, each bit requires both current nodes to be nonzero and to have the same tag; the checker then follows that child on both sides. After the last bit it requires either exactly one node to be zero or two different tags. A mismatch before the list ends is rejected as trailing witness data. The empty list is therefore precisely a witness of a mismatch already at the root.

Soundness follows backwards along the path. The terminal pair has different values by the preceding normal-form facts. At each preceding equal-tag pair, a child-value difference forces a parent-value difference by Cantor injectivity. Thus any accepted path proves inequality of the starting values, even if the arena contains arbitrarily many duplicate positive nodes.

Completeness is also finite. If the roots have different values, a zero/tag mismatch terminates immediately. Otherwise the roots have the same nonzero tag and at least one unequal-valued child; choose that direction. Both indices strictly decrease at every step, so this process terminates at a mismatch. Its length is bounded by the smaller root's unfolded height, hence by the number of arena nodes. If the root values agree, no accepted path exists. `find_path` is a producer implementing this search; the verifier never calls it.

Each bundle row carries exactly two paths, for `(c,a)` and `(c,b)`. The verifier checks both before evaluating the exact original bundle template. It does not replace freshness with pointer inequality or assume that different IDs have different values.

## All rule cases and the endpoint

The source50 mapping is unchanged: truth tag 0, MP tag 1, GEN tag 2, the eight original logical rows tags 3..10, and the CP/GIC/IR/vacuity bundle tag 11 with both freshness gates. The constructor arities and templates are imported unchanged from the copied source50 implementation.

The verifier evaluates templates using a frozen linear first-match lookup. A constructor request returns an existing node with exactly the requested tag and child IDs, or rejects. `B0(0,0)` returns0 and the only template literals are 0/1. An induction through each fixed template gives its correct denotation independently of how many duplicate nodes exist. No constructor is inserted or interned by the verifier.

For MP, the recorded major root must be the exact ID returned by the implication template on the minor and proposed result. This sufficient equality check establishes the numeric MP premise. GEN and every leaf similarly have their exact C254 denotations. The two accepted bundle paths establish the original numeric disequalities. Induction on proof-row order therefore yields an actual numeric C254 derivation of every accepted row value. With no trusted `goal` argument the final ID is the first literal `B1(0,0)` ID, so any accepted default certificate proves exactly numeric 1, the fixed falsity target. A certificate field named `goal` has no effect. An explicit trusted caller goal exists solely for positive controls and is a different acceptance question.

The converse uses source50's ordinary numeric-C254-to-interned-ground-certificate construction. Its arena has no duplicate keys, so first-match lookup selects exactly the original IDs. Each valid bundle's unequal parameters has finite distinguishing paths by the preceding lemma. Adding those two witnesses leaves all equality tests and the final F ID intact, yielding an accepted default certificate. Thus, at the level of ordinary finite mathematics,

`there exists an accepted default path certificate iff C254 proves 1`.

This is a completeness argument for existence of certificates. It does not claim that every duplicate-containing encoding of a valid derivation will be accepted. First-match lookup and ID-based equalities can reject an encoding that chooses different but equal-valued copies. An interned producer supplies complete encodings without requiring the verifier to certify global uniqueness. The provided executable conversion `from_term` assumes its source is an accepted source50 certificate; it is a producer, not a replacement source validator.

## Executable controls

The maintained runner prepares the following layout outside the checkout and runs:

```sh
uv run --no-project python -B test_paths.py
```

Python 3.13.14 passed in 0.664 s:

- All12 exact source50 rule controls convert and verify at their explicit positive goals; all reject at fixedF. A quoted canonical GEN conversion also passes.
- An unused duplicated positive constructor key is accepted by the new checker and rejected by the original uniqueness-checking source50 checker.
- Two genuine fully constructed bundle rows have pointer-distinct but equal-valued `c/a` or `c/b`; each is rejected at its respective path gate.
- A genuine bundle with a 2,048-edge distinguishing path passes using 4,160 arena nodes. No intermediate natural value is materialized. All31 bit paths of length at most 4 reject a pair of duplicated equal leaves.
- Truncated/trailing/bad-type paths, a forbidden zero alias, self-reference, bad tag/reference, false formula, empty proof, false MP and missing gate paths reject.
- 10,201 ordered pairs in an independently generated small arena agree with a test-only natural-value oracle on path existence, including duplicate values.
- All15 positive controls and their fixedF negatives still behave correctly while numeric pairing/unpairing/materialization, canonical verification and all producer APIs are patched to raise immediately if called.

The deep bundle required 297,059 first-match lookup record visits. The new checker has eliminated global key uniqueness validation, not all scans: fixed template lookup can still take quadratic total work, and there can be many bundle-path witnesses. The old source50 Python dictionary check was already convenient on a host computer; the proposed benefit is an opportunity for a simpler low-level verifier, not a demonstrated Python speed or asymptotic improvement.

## What remains before a machine claim

This gives a concrete alternative verifier interface: local backward-reference validation, fixed-template node lookup, sufficient pointer equality and two synchronized root-to-leaf paths per bundle. It avoids requiring the verifier to maintain or certify a globally interned arena. A fair finite-certificate search can in principle enumerate witnesses directly, without running an interning producer or a complete term equality algorithm.

A binary codec, a complete low-level implementation of all these operations, its fair enumeration/reset protocol, its complete state cost and a compiler/runtime proof have not been supplied. Template lookup and witness-list traversal must both be priced. No claim is made about a smaller machine, PA internalization, a new equiconsistency calibration, or a replacement for the checked 252-state baseline.

The maintained constructor-witness verifier in `term_circuits.py` supersedes this lookup interface. It retains the path argument while replacing first-match scans with explicit constructor-record IDs. `term_codec.py` then supplies a finite word parser and fair search specification. See the parent README for their scope and reproduction; the operation counts above remain the historical first-prototype evidence.
