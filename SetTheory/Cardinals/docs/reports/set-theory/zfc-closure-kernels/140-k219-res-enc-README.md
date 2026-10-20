# Equality discovery and independent diagnostics

The accepted source is tree 10 (zero based) in `eq_clean_hits.json`. Its
unbounded proof is `../../report/sections/equality.tex`. The deterministic
source builder is `../../portable/build_source219.py`; it needs no search.
The accepted machine uses only this macro replacement and the documented
literal transition patch.

`eq_superopt.cpp` is the finite-signature discovery search. With a C++17
compiler, its original run can be repeated from this directory:

```sh
g++ -O3 -std=c++17 eq_superopt.cpp -o /tmp/k219-eq-search
/tmp/k219-eq-search atoms.in /tmp/k219-eq-nodes.txt 7
```

The input file contains signatures over counter values 0 through 9, with an
unknown value for overflow or a detected loop. The root goal screen uses
values 0 through 4. `atoms.json` gives the corresponding literal library
fragments; `search7.log` is the original progress receipt. Root cost seven
skips the cost-six layer, so it does not cover the 0+6 or 6+0 root splits.
Semantic deduplication and finite observations are discovery heuristics.
No lower bound or unbounded equivalence follows from this search.

`verify_clean_eq.py` independently compiles the 16 recovered trees to an
address/interval control-flow graph and checks 1,750 pairs for each, including
all pairs through 40, nonzero unrelated registers, and larger cases through
10,000. Its receipt is `clean_eq_finite.json`. Run it with Python 3 and
assertions enabled. These finite diagnostics are separate from the report's
proof for every natural pair.

`audit219_boot.py` is a separately written complete blank-start verifier
using two dense tape halves. From the packet root:

```sh
python3 -B research/encoding/audit219_boot.py \
  machine/k219.native.tm /tmp/k219-independent-boot.json
```

The other development audit receipts in `../../verification/` are provenance
records of independent reviews. The supported portable release checks are
in `../../portable/`; default replay rederives the complete final runtime.

Two additional development audit scripts are included with their receipts:

```sh
python3 -B research/encoding/audit_final219.py \
  machine/k219.native.tm machine/sites219.json /tmp/k219-literal-audit.json
python3 -B research/encoding/audit_runtime_certificate.py \
  machine/k219.native.tm machine/sites219.json \
  verification/development_runtime.json portable/reference_results/cases.json \
  machine/legacy_mapping.json /tmp/k219-runtime-report-audit.json
```

The latter consumes the original development receipt format. It checks exact
head displacements and source suffixes independently; it is a structural
audit of the completed symbolic result, not another symbolic proof engine.
