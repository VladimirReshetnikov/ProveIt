# A Cut-Sensitive Attack on the First Open MIX Grammar Case

Research report prepared for Vladimir Reshetnikov, September 20, 2026.

## Outcome

The selected open question is whether `L_3 = MIX` for the canonical tuple
grammars in Takao Yuyama, *On the Kanazawa–Salvati Conjecture*,
arXiv:2609.13871v1 (September 12, 2026).

**That open question is not solved in this report.** The package contains
complete written proofs of a cut-sensitive membership recurrence, a broad
three-component positive family, and an infinite family in `L_3 \ L_2`.
It also contains a completed exhaustive computation through length 21.
The universal proofs have not been formalized in a proof assistant. The
finite frontier is software-assisted, not a formal certificate covering
all enumerated decisions. Bibliographic priority for the extensions has
not been established.

The published word `aaabbbcbbccccaa` is explicitly credited to Yuyama. Its
occurrence as the first member of our infinite family is not presented as
a new discovery. The one-sided binary inclusion is also credited to the
proof of Yuyama's Proposition E.3.

## Read first

- `mix_grammar_report.pdf`: the 20-page article.
- `mix_grammar_report.tex`: complete LaTeX source, including bibliography.
- `references.bib`: reusable bibliographic entries (not required to compile).
- `RESEARCH_STATUS.md`: claim-by-claim verification and scope.

## Mathematical results

Write `A_r` for the canonical r-tuple grammar and `L_r = concat(A_r)`.
The article proves:

1. The exact backward membership recurrence: endpoint peeling, extraction
   of a balanced interval with induced cuts preserved, and inverse
   regrouping by one-cut refinement.
2. `(a^p, v, a^(N-p))` belongs to `A_3` for every binary word `v` with
   `N` b's and `N` c's and every `0 <= p <= N`.
3. With `N=p+u` and positive parameters `p>s`, `u>r`, and `r != s`,
   `a^p b^(N-s) c^r b^s c^(N-r) a^u` belongs to `L_3 \ L_2`.
4. In particular, `a^(3m) b^(3m) c^m b^(2m) c^(4m) a^(2m)` has
   canonical rank exactly three for every positive integer m.
5. The displayed parameter region has
   `binomial(N-1,3) - floor((N-2)^2/4)` distinct words of length `3N`.
   The canonical language `L_2` is not closed under cyclic rotation.

“Canonical rank” is not the minimum fan-out of an arbitrary grammar for
a singleton language. The full Kanazawa–Salvati conjecture is not resolved.

## Requirements

Python 3.10+ with the standard library; no pip packages are needed.
A C++17 compiler is needed for the large enumeration. A standard LaTeX
installation is needed only to rebuild the PDF. The supplied PDF can be
read without installing any of these tools.

## Individual membership queries

```sh
python src/mix_parser.py 2 aaabbbcbbccccaa   # accepted: false
python src/mix_parser.py 3 aaabbbcbbccccaa   # accepted: true
python src/mix_parser.py 3 a accb b           # accepted: false
python src/mix_parser.py 2 aaccbb             # accepted: true
```

**Each positional word after the arity is one component.** The last two
examples illustrate that forgetting component cuts gives a wrong parser.
No components means the empty normalized tuple. Empty components may be
omitted. Public Python methods validate the alphabet and arity.

```python
from src.mix_parser import Parser
p = Parser(3)
assert p.accepts_word("aaabbbcbbccccaa")
assert not p.accepts(("a", "accb", "b"))
```

Cache limits change performance, not the mathematical decision. No node
budget or probabilistic approximation is used by the production programs.
Large individual words may run out of ordinary machine resources or
Python recursion depth; such an exception is not a rejection certificate.

## Reproduce the checks

```sh
make check
```

Or run the components separately:

```sh
python tests/forward_oracle.py
python tests/test_results.py
python tests/check_recorded_results.py
python src/check_certificate.py certificates/separation_m1.json
```

`forward_oracle.py` generates exact fixed-arity tuples using only the
original forward rules and compares every balanced tuple through length
six with the backward parser. It checks arities one, two, and three.
`test_results.py` checks structural examples, all obstruction-region
parameters through N=12, and 1,965 independently checked positive
certificates for the two-ended binary family through N=5. It also checks
that a deliberately corrupted certificate is rejected.

## Reproduce the exhaustive frontier

```sh
python src/exhaust_python.py 6 > data/reproduced_python_through18.json
mkdir -p build
c++ -O3 -std=c++17 -Wall -Wextra src/exhaust.cpp -o build/mix_exhaust
build/mix_exhaust 7 > data/reproduced_cpp_through21.json
```

The numeric argument is the maximum number of occurrences **per letter**;
7 means total length 21. The C++ command writes progress to standard error.
Its final JSON must be complete, with closing braces. A header in a
truncated or interrupted file does not establish completion.

Saved results:

| Length | Balanced words | Rejected by L2 | Rejected by L3 |
|---:|---:|---:|---:|
| 0 | 1 | 0 | 0 |
| 3 | 6 | 0 | 0 |
| 6 | 90 | 0 | 0 |
| 9 | 1,680 | 0 | 0 |
| 12 | 34,650 | 0 | 0 |
| 15 | 756,756 | 84 | 0 |
| 18 | 17,153,136 | 3,672 | 0 |
| 21 | 399,072,960 | 111,564 | 0 |

The runs account for 417,019,279 balanced words in total. The Python
implementation reproduces all rows through length 18. C++ checks one
representative per alphabet-renaming/reversal orbit; orbit weights are
checked against `(3N)!/(N!)^3`. The Python enumeration uses only alphabet
renaming. Both transfer positive level-two results to level three by the
proved monotonicity, rather than separately querying all level-three words.

`data/cpp_final_through21.json` and `data/cpp_final_exhaust.log` come from
the final, readable C++ source. The preceding implementation's completed
run is also retained as `data/cpp_through21.json` / `data/cpp_exhaust.log`.
The row for length 21 took about 96 seconds in the final recorded run;
the Python length-18 row took about 74 seconds. These are observations
from this environment, not portable performance or memory guarantees.

## Construct and check positive certificates

```sh
python src/family_certificate.py bbbcbbcccc 3 > new_certificate.json
python src/check_certificate.py new_certificate.json
```

The JSON records only original empty, wrap, and binary-regroup rules.
The checker does not call the membership parser or assume the family
inclusion theorem. Included certificates cover m=1, 2, and 5 in the scaled
separation family. These certificates establish positive membership in
A3. The universal negative A2 proof is in the article.

## Build the article

```sh
make pdf
```

The LaTeX bibliography is embedded in the `.tex`; BibTeX is unnecessary.
The make target uses three pdflatex passes to settle the contents and
cross-references. No font files or third-party article PDFs are bundled.

## Integrity

No checksum manifest is bundled: re-running the verification scripts or
rebuilding the PDF changes file hashes, so a stored manifest would go stale
on the first rebuild.

Rebuilding a PDF or rerunning timed experiments will naturally change its
hash. Hashes verify file identity, not mathematical or software correctness.
Original run logs, independent checks, and the exact scope of the results
are retained so that those distinctions remain visible.
