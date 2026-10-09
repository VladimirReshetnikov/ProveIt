# Sparse certified port incidence

A research continuation for `ProveIt/Topology/UnknotRecognition`, dated
8 October 2026. Start with **article/sparse_port_incidence.pdf**; the complete
LaTeX source and generated tables are beside it.

## Result and scope

The inspected maintained incidence interface uses a dense `2**r` Boolean
inversion, even when only a few component signatures occur. This package
recovers exactly the occurring signatures through the same unweighted
coning/orbit-count interface, without knowing their number in advance.

The article proves sparse recovery, an output-sensitive balanced-block query
bound, independent minimal-support certificates, and an explicit polynomial
support bound for interval-encoded marks. It also proves exact coning and
union re-marking updates and a support-preserving binary-cover refinement.

The polynomial support conclusion uses **classical weighted AHT theory**.
This is not the first polynomial weighted orbit algorithm. The contribution
is a sparse, independently certifiable black-box route through the maintained
unweighted kernel, improving the inspected dense interface's representation
bound. It does not prove general quasi-polynomial unknot recognition.

## Executed versus not executed

**Executed:** 19 unittest methods, including 6,654 exhaustive nonnegative
histograms, randomized abstract and interval systems, signed covers,
adversarial certificate checks, and huge binary inputs. Raw component
benchmarks retain 273 measurements plus 39 warmups, with identical dense
controls, sparse strategies, and a full-support regression.

**Audit boundary:** component benchmarks run the explicitly labeled extraction
in `tests/aht_reference.py`. They do not run an unchanged full ProveIt checkout.
Dense and sparse arms use the same extracted count kernel and union cache.
Small outputs are checked by literal connectivity; huge static/periodic
outputs have independent endpoint/residue checks.

**Adapter boundary:** `sparse_ports/proveit.py` is an opt-in adapter to the
maintained count and independent proof-replay APIs. Its executed contract
tests inject independent literal count witnesses. Genuine maintained AHT
trace integration, the full maintained suite, native normal-arc benchmarks,
and whole-knot performance measurements were **not executed** in this delivery.
The native integration smoke script is supplied for that next step.

## Reproduce standalone results

Python 3.10 or later; the retained run used CPython 3.13.5. No third-party
Python dependency is needed.

```sh
python -m unittest discover -s tests -v
python benchmarks/run_benchmarks.py --output results/benchmarks_rerun.json
python benchmarks/make_tables.py
cd article
sh build.sh
```

`make_tables.py` reads the **retained** `results/benchmarks.json`, not the new
unreviewed timing rerun. `article/build.sh` needs a TeX installation with
pdfLaTeX, newtx fonts, amsmath/amsthm, mathtools, microtype, booktabs, enumitem,
listings, hyperref, and fancyhdr. The article's bibliography is self-contained;
BibTeX is not needed. `reproduce.sh` combines the commands.

## Small standalone use

```python
from sparse_ports import recover, certificate_payload, verify_payload

true_profile = {0: 2, 1: 3, 6: 5, 7: 7}
def exact_zeta(mask: int) -> int:
    return sum(w for t, w in true_profile.items() if t & mask == t)

result = recover(3, 17, exact_zeta)
assert result.as_dict() == true_profile
assert verify_payload(3, 17, certificate_payload(result), exact_zeta)
```

This example illustrates the **algebraic oracle contract**. A real certificate
must authenticate each zeta value from its original interval input; arbitrary
producer-supplied numerical answers are not self-authenticating.

`examples/worked_profile.json` and `examples/huge_static.json` are tagged-hex
examples. Read them with `sparse_ports.codec.loads`. The huge example is a
compressed capacity example, not a hard knot or a native AHT trace.

## Proposed integration

Place this directory, initially, at:

```
Topology/UnknotRecognition/research/sparse_port_incidence/
```

No existing file needs to be overwritten. From this package directory run:

```sh
python integration/native_smoke.py /path/to/ProveIt --cases 250
```

That command imports the real maintained kernel, compares dense and sparse
profiles, records genuine local orbit proofs, independently replays them,
and checks replay with the producer disabled. It was **not run here**.
See `integration/INTEGRATION.md` for contracts and promotion gates.

## Evidence and files

`results/benchmarks.json` contains raw samples, query counts, platform details,
and hashes recorded by the benchmark driver. `results/tests.txt` is the
executed standalone log. `results/article_build.txt` records the PDF build.
`provenance.json` identifies the exact inspected repository blobs and the
baseline incidence integration commit; it does not mislabel that commit as
the current overall repository head. `claims.json` distinguishes proved,
implemented, measured, imported, and remaining statements. `SHA256SUMS`
covers the distributed files other than itself.

The source and artifacts are offered under MIT-0. The audit kernel retains
attribution to the inspected MIT-0 ProveIt source. No third-party article PDFs,
font files, or unchanged full repository snapshot are redistributed.
