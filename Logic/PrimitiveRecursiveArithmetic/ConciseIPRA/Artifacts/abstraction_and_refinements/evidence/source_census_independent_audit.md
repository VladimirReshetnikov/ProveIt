# Independent static audit of the frozen source census

Commit: `167c76930834c17648fcc2509ab16260da4c727d`. Interpreter: CPython 3.12.14.

## Result

I found no complete ordinary standalone checker below any coordinate of the currently exhibited compact envelope **244 significant Python tokens / 265 AST nodes / 477 normalized UTF-8 bytes** in the frozen artifact sources and seven incoming archives. This is a census result about the inspected corpus, not a mathematical lower bound or a claim of global optimality. The three coordinates belong to different programs; they are not the size of one program. The underlying compact protocols also differ.

## Coverage and independent recomputation

The audit covers all **2,792 artifact `.py` path instances**, represented by **1,624 distinct Git blobs**, plus **99 `.py` path instances in the seven extracted incoming archives** (including duplicated controls). All sources were parsed successfully. Every artifact blob's Git SHA-1 was independently recomputed from `b'blob ' + decimal_length + b'\0' + raw_bytes` and matched its pinned identity.

I independently recomputed every source metric, using symbolic `tokenize` constants. The normalization removes initial docstrings from modules, classes, functions and async functions, then uses `ast.unparse(tree) + '\n'`. Significant tokens exclude `ENCODING`, `ENDMARKER`, `NEWLINE`, `NL`, `INDENT`, `DEDENT` and `COMMENT`. The AST measure counts every node returned by `ast.walk` on the stripped tree; bytes are the UTF-8 length of the normalized source. The independent measurements agree with **all 1,624 entries** of `evidence/artifact_source_census.json`; there are **zero metric mismatches**.

The independent script only reads, hashes and parses the downloaded programs. It does not import or execute them. Its initial census was subsequently aligned with the repository's docstring-removal convention; the current saved JSON and this report use that convention throughout.

## Exhibited compact witnesses

| Corpus and witness | Tokens | AST nodes | Bytes | Input contract visible in source |
|---|---:|---:|---:|---|
| Frozen artifact: `checked_presentation/second_delivery/code/checker_tokens.py` | 244 | 272 | 608 | Streaming JSON lines, consumes the required certificate prefix |
| Frozen artifact: `checked_presentation/second_delivery/code/checker_ast.py` | 249 | 267 | 606 | Streaming JSON lines, consumes the required certificate prefix |
| Frozen artifact: `zero_test_split/checker/code/compact478.py` | 271 | 305 | 478 | Buffered JSON array; records popped from its end |
| Incoming Boolean constancy: `checkers/code/checker244.py` | 244 | 272 | 604 | Streaming JSON lines |
| Incoming fused iteration: `code/checker_refinement/checker.py` | 249 | 265 | 605 | Streaming JSON lines |
| Incoming head conversion: `code/compact477.py` | 272 | 306 | 477 | Buffered JSON array; records popped from its end |

The artifact-only coordinatewise envelope is **244 / 267 / 478**. Including all seven incoming archives gives **244 / 265 / 477**. None of these compact sources is being reclassified here as a full public grammar validator with mandatory end-of-input consumption. In particular, the streaming and buffered contracts must be identified separately in comparisons. A complete source for its stated compact contract is not automatically a validator for arbitrary malformed JSON or a strict whole-input protocol.

Exact identities of the first three witnesses are Git blob SHA-1s `49f77d7ece8a4f8d9df6aab67037d7832f4443ea`, `815a2582ada1599520a05472db81bfbc05dcacb2` and `58e53917f72688a48e930230e32de5d52ce95b83`. The incoming AST witness has SHA-256 `a2e6562dd87294aefe052358df5991b10ad1d693c51742dc5865064fdf071cdd`; the incoming byte witness has SHA-256 `8c4e4ce67c87e9b90ed9e37e1162c9ef801dc77549c738ebcd04b06458746575`.

## Subfrontier classification and exclusions

There are **131 source records** whose token, AST or byte measure is strictly below at least one coordinate of 244 / 265 / 477. None contains the literal acceptance constant `ACCEPT`. That absence was used only as a screening aid: their imports, calls, declarations and relevant source were also inspected so a differently spelled acceptance marker would not by itself exclude a checker.

Two of the 131 are packed execution wrappers, each measuring **18 tokens / 19 AST nodes / 459 bytes**:

- `502_scope_audit/illustrations/checker_packed.py`, Git blob `751bd35a260d687333a878f3f6fd45515749aee2`;
- `502_scope_audit/illustrations/incumbent_506_packed.py`, Git blob `434346c0d5c1e79fd0b1d89134f1836a5d524d56`.

Both call `exec(zlib.decompress(base64.b85decode(...)))`. They store and expand another program as compressed data. They are excluded from the ordinary uncompressed source comparison; this exclusion is explicit rather than silently treating their small AST as a new inference kernel. They were not executed.

The remaining 129 subfrontier records are support code: source-size utilities, PDF/report builders, manifest/hash checks, certificate serializers and coordinate converters, reproduction/test launchers relying on other files, finite mathematical experiments, or imported protocol helpers without a standalone proof acceptance path. Representative cases checked directly include:

- `single_binder/code/to_one_line.py`: JSON load/dump serializer;
- `uniform_raw/reproduce.py` and `evaluation_discharge/zero/verify.py`: external-program launchers;
- `checked_presentation/second_delivery/to_stream.py`: alphabet/format checking and serialization, without proof inference checking;
- `backward_replacement/ipra_backward_replacement/grouped/translate.py`, `zero_test_split/checker/compile_certificate.py`, and incoming head-conversion `convert477.py`: certificate conversion;
- `coverage_and_kernel/tests/protocol.py`: a protocol helper, not a standalone checker;
- `compact_update/closure_criterion.py`: a finite mathematical experiment;
- `counter_congruence/build.py`: TeX/PDF builder;
- `scope_and_closure/measure.py`: source measurement utility.

The last two enter the subfrontier list only after the agreed docstring removal; both have been checked directly. The full subfrontier list is saved in `evidence/subfrontier_sources.json`, and the independent complete measurements are saved in `evidence/source_census_independent.json`.

## Limits of the audit

This census does not independently prove soundness and completeness of every submitted checker. It rules out an overlooked smaller ordinary standalone acceptance module among the inspected subfrontier candidates, and verifies the exhibited source measurements. Mathematical soundness, public syntax validation, proof-domain assumptions and strict whole-input behavior remain separate obligations. No broader minimum for public or strict validators is asserted here.
