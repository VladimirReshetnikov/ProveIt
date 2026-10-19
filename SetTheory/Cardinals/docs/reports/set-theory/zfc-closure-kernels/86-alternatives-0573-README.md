# Exact C254 certificates with local constructor witnesses

The latest [fixed-pattern matcher](pattern-matching.md) removes the supplied
constructor witnesses as well. It checks a claimed formula directly against the
trusted axiom pattern, handling zero normalization explicitly. The small bundle
certificate shrinks from 4,582 to 2,506 bits, at the cost of more constructor
reads. Both protocols and their comparisons are retained below; neither has a
compiled TM state count.

This experiment removes two verifier obligations from source50's constructor-term frontend: global arena-key uniqueness and template-node search. Every schema instead supplies IDs for the fixed template's constructor records. The two bundle freshness conditions carry finite distinguishing paths. A total finite-word codec and a fair length-lex search specification are included. The ordinary arguments below preserve refutation completeness for the **full twelve-rule C254 calculus**, including native equality and both freshness gates. No complete binary TM, state count, Lean proof or PA/ZFC internalization is claimed.

The source is source50, *Canonical term certificates for small consistency machines*, received as `docs/incoming/zfc_sparse_certificates.zip` in `85633fd2f57b5dca16f87667699134d1b500ebc0`, with historical ProveIt pin `fab89c5d26b81cd2ccab2ee5d213ff23725c7726`. Its unchanged fixed specification is hosted at `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/50-terms-data-spec254.json`. The new code is ProveIt research following that delivery. Mira-Cult's original calculus/machine, Jeff Ketchersid and contributors' verification, Andrew James Wade's framework, mira-emmy's 253 reduction and ProveIt's 252 permutation/bootstrap/formalization retain their attribution. This is a new frontend experiment and does not modify the checked 252 machine.

## Reproduce without a delivered checkout

From the repository root:

```sh
uv run --no-project python -B Computability/BusyBeaver/Research/ZFC/check_term_certificates.py
```

The runner invokes the maintained `reproduce_157.py --prepare-only` helper to recover source50 offline from its committed archive and unchanged hosted ancillaries. It copies nine experiment files into a fresh directory outside the checkout, arranges the recovered `source50/code` and `source50/data` layout, and runs `test_paths.py`, `test_circuits.py`, `test_codec.py` and `test_patterns.py` sequentially with assertions enabled. The first test generates the deep fixture used by the later suites. A separate clean process then loads the actual hosted fixed spec and runs both verifier/codec protocols with no numeric or producer modules imported. `--repo` supports a runner outside the checkout; `--output` selects a new or empty external evidence directory.

No original source50 files are copied into this publication directory or edited. The recovered code is used only by test/producer adapters; both verifier/codec protocols use only the standard library and explicit trusted fixed templates. No network, Lean/Coq build, incoming checksum-manifest loop or machine search runs. The output `verification.json` records exact commands, source/spec identities, all four result objects and the independent-process replay. Logs and generated controls remain outside the checkout.

## Normal arenas and two exact disequality witnesses

The arena starts with the sole zero record `0:Z`. Every positive record is `Btag(left,right)`, tag 0..3, with strictly earlier child IDs. Only `B0(0,0)` is forbidden. **Duplicate positive records are permitted.** The ordinary denotation is

`value(Z)=0`, `value(Btag(x,y))=4*P(value(x),value(y))+tag`,

with the exact C254 orientation `P(a,b)=(a+b)(a+b+1)/2+b`. The verifier never evaluates this denotation. Induction makes ID 0 the sole zero-valued record: any positive tag has positive value, while a tag 0 record has a nonzero child and therefore positive Cantor value. Reduction modulo4 identifies a nonzero record's tag; Cantor injectivity then identifies its child values. Thus unfolded normal trees represent equal naturals exactly when they have the same constructor tree. Different IDs may nevertheless represent the same tree/value.

A disequality witness is one finite left/right path. Each bit requires two nonzero records with the same tag and descends that child on both sides. At the end, exactly one root must be zero or their tags must differ. A mismatch before the end rejects trailing witness data. Terminal values differ, and constructor injectivity carries the difference backwards along the path, proving soundness even with arbitrary positive duplicates. Conversely unequal values either mismatch now or have an unequal child; strictly decreasing indices make that search terminate. No equal-valued pair has an accepted witness. Every bundle row supplies two paths, for `(c,a)` and `(c,b)`.

## Constructor circuits and exact rule transport

The fixed source50 terms are expanded once into finite postorder circuits. Initial registers are the rule parameters and zero. Each subsequent instruction names a tag and two earlier circuit registers; the certificate supplies an arena ID for its result. The verifier checks only that indexed record's literal tag/child IDs, or result ID 0 for normalized `B0(0,0)`. Static sharing is over the finite trusted symbolic templates, never an index or uniqueness test over the candidate arena.

Truth's result is 0. MP directly checks the major is normalized `B0(minor,proposed result)`, including the legitimate all-zero alias. GEN directly checks `B2(binder,premise)`. All eight logical templates and the complete bundle are retained exactly; the bundle additionally checks both paths. Schema circuits have 5,6,5,5,5,6,5,6 constructor instructions, and the full bundle has 62 including shared F. These are interface counts, not physical control states.

Induction through each circuit gives its intended numeric denotation; then induction over proof rows gives an exact C254 derivation. ID equality is used only as sufficient equality, never ID inequality as a semantic freshness test. The default endpoint directly recognizes **any** `B1(0,0)` record, whose value is 1. The certificate cannot choose its goal or templates. A trusted caller-selected goal exists only for positive controls; the binary acceptance/search interface supplies no such argument.

For existential completeness, use source50's ordinary construction of an interned arena from a numeric C254 proof. Every template record exists with consistent IDs; valid bundle parameters have finite distinguishing paths. Supply the existing IDs for each circuit instruction. The resulting certificate is accepted and its last root is F exactly when the numeric proof concludes 1. Thus an accepted default certificate exists iff C254 derives 1. This does not say every duplicate-containing representation of a valid proof is accepted: MP can reject numerically equal child copies with different IDs. The interned producer suffices for existence without requiring the verifier to certify uniqueness.

## A finite binary codec and fair search

A natural field is unary `1^n0`. The sole Z node is implicit. A word contains the unary positive-node count; each node has a 2-bit tag and two unary child IDs; then a unary proof-row count. Each row has a 4-bit rule tag, its fixed-arity argument/premise IDs, a formula ID and, for schema rows, the trusted fixed number of circuit IDs. The bundle has two paths coded end=`0`, left=`10`, right=`11`. Unknown rule tags 12..15, forward/out-of-range references, zero aliases, truncation and leftovers reject. The parser can accept structurally well-shaped but logically false rows; the exact verifier decides their rule/gate validity.

Counts are bounded by bits physically present before allocating records: a unary count consumes that many 1 bits, and additionally `4*N <= remaining_bits` is required for node count N and `5*P <= remaining_bits` for row count P. Fixed arities/circuit lengths are trusted constants; paths append only after consuming a symbol. No claimed count preallocates a candidate-sized array. All parsing loops consume finite input or use a fixed arity, so every finite word terminates. Resource failures propagate and are never reported as consistency or logical rejection.

Field inversion and induction over finite records prove `decode(encode(c))=c` for every structurally valid canonical certificate, without logical-validity assumptions. Conversely every successful parse consumes exactly the whole word and re-encodes identically. A word of length L and binary value v has rank `2^L-1+v` in the fair length-lex enumeration. Consequently, in the usual unbounded-resource finite-algorithm interpretation, default search returns a word iff C254 derives 1. The separate bounded search labels no-hit results by their tested maximum length; it does not return consistency.

Unary addresses sacrifice compactness: the 2,048-edge bundle control uses 9,042,403 bits and the small bundle(0,1,2) uses 4,582. This codec does **not** retain the delivery's O(L²) certificate-bit bound. Its purpose is a simple exact interface to price and compile later.

## Verification and remaining cost

The three original scratch suites passed. The maintained runner repeats them freshly and records current timings:

- Path prototype: all 12 rule tags/15 positive controls, both different-ID/equal-value gate attacks rejected, a 2,048-edge path, 10,201 independent small-denotation pair checks and disabled-arithmetic controls.
- Circuit prototype: 261 fixed-template comparisons with source50 over all parameter collisions in 0/1/2, duplicate GEN/schema outputs, both F copies, malformed local witnesses and disabled lookup/producer APIs. The 4,160-node deep bundle uses 4,159 local node checks,62 supplied-record checks and2,048 path edges. The first prototype visited 297,059 records for template lookup on the same example; its original method/counts are retained in [history-path-lookup.md](history-path-lookup.md).
- Codec: all 15 positive-control roundtrips/defaultF negatives; 16 malformed words and all proper prefixes of the 8-bit truth control; all 262,143 words of length at most 17 decoded, with 93 successful exact re-encodings and no fixedF acceptance. The latter is finite evidence only. Scheduling/rank and resource-exception controls also pass.

Eliminating a verifier obligation does not establish a state saving. Indexed reads still need tape access; fixed circuits need data/control representation; proof parsing, witness traversal, enumeration, reset and blank initialization all need implementation and a complete price. The scripts are not a verified compiler, complete binary machine, internal arithmetic checker or new consistency calibration. The checked 252 baseline remains unchanged.

Independent review found and corrected one resource-policy mismatch before publication: the two experimental verifier catch lists initially included `RecursionError`. That exception is now allowed to propagate, and the codec test injects both `MemoryError` and `RecursionError` inside the actual core constructor check. This changes resource reporting, not any normal finite-certificate result.
