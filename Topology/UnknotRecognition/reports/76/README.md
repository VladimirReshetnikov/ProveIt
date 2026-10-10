# Disk-Transfer Algebras and Binary-Compressed Patch Search

Research continuation for ProveIt's unknot-recognition programme, 9 October 2026.
Reviewed repository pin: `cd984a34c0e06e467f3403576afbe6deeb1b5d11`.

The article proves an exact algebraic and algorithmic improvement for **supplied finite patch grammars**. It does not establish a general quasi-polynomial unknot recognizer, and the reference software does not return native knot verdicts.

## Main results

For disk-union transfers with `a` input and `b` output intervals, modulo all whole-disk cap queries,

    Hom(a,b) = Mat_(2^(b-1) by 2^(a-1))(F_2[epsilon]/epsilon^2).

The isomorphism is explicit, respects composition, and yields a trace formula for disk completion. Actual candidates remain actual candidates: formal XORs of surfaces are not witnesses.

For a homogeneous acyclic grammar of width `b`, `q` XOR charges, literal binary repetition exponents, structural encoding size `N`, and atomic cost bit length `B`, put `R = q * 2^(2*b-1)`. All-cap scalar minimum-cost search takes `poly(N,b,B) * R^4` bit work by elementary elimination. A single library repeated `W` times uses `O(log(W+1))` composition stages. Choices in different copies are independent.

Every feasible optimum has an original-word witness DAG of `O(M + S*R)` nodes, where `M` is explicit library size and `S` compiled rule count. Run certificates reconstruct every local candidate source before checking no-more-expensive same-charge span inclusion.

A separate nonnegative **free-star** result bounds a shortest optimum by `R-1` layers. It must not be used to shorten a fixed physical span.

## Start here

- `article.pdf` / `article.tex`: complete 27-page article, proofs and research agenda.
- `docs/THEOREM_LEDGER.md`: exact theorem and implementation status.
- `docs/INTEGRATION.md`: source adapter obligations and scope of negative answers.
- `docs/REVIEW.md`: review risks, counterexamples and development corrections.
- `docs/SOURCE_AUDIT.md`: prior work, provenance and access limitations.

## Reproduce

Python 3.10 or later is intended; the actual recorded run used CPython 3.13.5. Only the Python standard library is required. A standard TeX Live installation with `latexmk` builds the PDF.

```sh
python -m unittest discover -s tests -v
python code/audit.py --output data/audit-rerun.json
python code/benchmark.py --output data/benchmarks-rerun.json \
  --csv data/benchmarks-rerun.csv --repeats 3
python code/compressed_search.py examples/huge_repetition.json \
  --certificate examples/huge-rerun.cert.json \
  --output examples/huge-rerun.result.json
python code/checker.py examples/huge_repetition.json examples/huge-rerun.cert.json
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The complete benchmark is slower than the ordinary test/audit suite. Run selected workloads with, for example, `--select b2_q2_W2,b2_q2_W4096`. Timings, runtime strings and test elapsed times are not expected to reproduce byte-for-byte. Use new output paths to preserve delivered evidence.

## Executed evidence

All 52 test methods pass. The deterministic audit records 44,168 disk-cap entries, 4,964 rectangular matrix products, 41,438 trace pairings, 14,400 weighted queries, 39,926 powered-versus-explicit cap/charge queries, 855 pair meshes, and 1,408 literal complete-word meshes across 80 fully enumerated source languages. The enormous-exponent control has `W=2^1024`, analytically verified optimum `-3*W+4`, 1,025 compiled rules, 4,096 composition pairs, and a 2,049-node reachable witness DAG.

The seven-case paired timing corpus includes a narrower one-sided baseline and a universal two-sided baseline. At width two and `W=4096`, powering is about 39.1 times faster than the one-sided baseline in this corpus. On a width-four four-layer control it is about 387 times slower. These are abstract-grammar measurements, not native recognizer timings. Raw source workloads and all measured samples are retained in `data/benchmarks.json`.

## Input semantics and safety boundary

Each partition uses canonical nonnegative block labels, with inputs before outputs. Each atomic surface is a union of disks, every component meeting an external interval. Gluings use actual separated proper boundary intervals. Compositions creating a cycle or a sealed component are rejected for the **whole-surface-is-one-disk** objective. Rooted disk-component search has different rules.

`power` means every occurrence independently chooses a word from its base language. Union branches must have equal physical span. Hidden eligibility predicates, conflicting global geometry choices, circle capping, shared interval endpoints and ambiguous arc multiplicities are not supported. Query charges refer to the module; shift them by a certified cap charge when necessary.

The CLI returns `FOUND_ABSTRACT_DISK`, `NO_DISK_IN_GRAMMAR`, or an explicit resource-limit status. The latter two are not knottedness certificates. Default allocation/work guards intentionally prevent unrestricted exponential requests. Parse errors and interpreter integer-conversion limits are not negative mathematical answers.

## Integration

This is an additive report package. Follow the current `docs/incoming/README.md` intake policy; the repository owner assigns the next `reports/<NN>/` location. No number, production patch, dispatch change or remote repository write is included. A native exporter and independent product-chart/source-bound embedding checker remain to be implemented. No standalone checksum manifest is supplied.

The code's parser/compiler is shared by producer and checker; graph topology and feature kernels are independent. The PL oracle checks abstract triangulated surfaces, not ambient embeddings. Mathematical proofs are self-contained but are not proof-assistant checked or externally peer reviewed.
