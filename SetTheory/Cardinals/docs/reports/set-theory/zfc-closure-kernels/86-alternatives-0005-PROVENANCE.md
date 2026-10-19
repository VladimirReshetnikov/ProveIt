# Provenance and license boundaries

This package records research based on ProveIt commit 7ba1598461c6e485c5aeb8f673c0b1d571f8012b:
https://github.com/VladimirReshetnikov/ProveIt/tree/7ba1598461c6e485c5aeb8f673c0b1d571f8012b

The local source HEAD was checked against that exact pin. The small unchanged source subset is listed and hashed in source-subset-manifest.json. The fixed template JSON itself retains its earlier originating source pin and hash; those inherited metadata are not silently rewritten to the checkout pin.

Authorship:
- Mira-Cult designed the original public 254-state machine, compact set theory/calculus, source program, and optimized interpreter.
- Jeff Ketchersid (jeff87654) supplied the imported Coq verification and related symbolic proof infrastructure.
- Andrew James Wade supplied the public compiler framework, under its separately retained MIT-0 notice.
- The inherited provenance credits the public 253-state reduction to mira-emmy.
- ProveIt supplied the later register-permutation, prefix/context reductions, logical formalization, and strict affine checking work used as the baseline.
- The present package contains the new experiments, component constructions, ordinary proof arguments, and independent reviews described by their files. It does not claim invention of inherited schema-reparameterization search freedom or authorship of upstream machines.

The ProveIt historical Jeff import is pinned to 297ab8df7e5de329605c3875b4934643b371a5e3. The user's public zf-254 branch reference also supplied pin c132d7eae8158cd3a9850ea3eb7251158c3dd821; that is a distinct reference, not the pinned imported bytes used by these experiments. Public reference:
https://github.com/jeff87654/busy-beaver/tree/zf-254/ZF/m254

The imported 254-state table hash is d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb. Its author source.py and paths.json were absent from the import. The original published verifier does not require them. No fresh end-to-end Coq compilation is claimed here.

No repository-wide license was declared for the pinned Jeff tree. ProveIt's blanket MIT-0 grant explicitly excludes unchanged upstream material. The included notices retain their original scopes; this archive makes no new claim to relicense upstream work. Wade backend copies remain under the retained Wade notice. The small ProveIt source subset carries its scoped original LICENSE.

Historical context only:
https://wiki.bbchallenge.org/wiki/Logical_independence

That page is not the proof of any candidate in this archive. No unconditional nonhalting theorem, Con(ZFC) proof, new Busy Beaver record, or complete sub-246 result is claimed.

## Subsequently supplied 245-state construction

The successful complete construction is the user's parallel research contribution associated with https://chatgpt.com/c/6ad42686-bb4c-83e8-a49b-947cc7786102 . It was supplied as `zfc245-proof-20261018.zip`, SHA-256 `5a38b0e7475905584eabcb75912caa8d5f4149148e8c2a2439b2702a9de49ba1`, and remains a separate unchanged artifact. Its inspected ProveIt source pin is `c6bf052c70bbbafba8c39370a6a2d123f57cd2c1`, distinct from this alternative project's pin. Independent comparisons show the relevant inherited calibration, parser, macro/affine engine, original source program, and logical seed agree with our reviewed baseline.

The present supplement claims independent audit and alternative research, not discovery of that 245-state machine. Its mathematical acceptance, runtime replay, literal startup and allocation/routing checks are documented in `audit245-addendum.pdf` and `research_sub246/verification/audit245_*`. The selected unchanged baseline dependencies are included only to make the independent checks reproducible without a full checkout. See `source-subset-manifest.json` for exact byte hashes and notices/ for retained upstream attribution and scoped license texts.
