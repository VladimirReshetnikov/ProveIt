UNIFORM ZERO AND CONSTRUCTED PREMISES FOR iPRA
10 November 2026

READ FIRST
==========
report.pdf is the complete paper; report.tex and its included .tex files
are the complete editable source. The report gives every primitive logical
and numerical rule and includes all inherited arithmetic/logical bridge
proofs with attribution.

The requested significant foundational breakthrough is NOT established.
The axiomatic basis is inherited. The positive new result is a uniform-zero
certificate presentation and construction of elimination majors, preserving
the full native consequence relation and its bi-interpretation with iPRA.

The pinned ProveIt commit is 76a2651601d17b34d46753f189ea026a21ce8d29.
All 17 current archives were inventoried. The supplied minimum was 558
normalized Python bytes, with separate minima of 262 tokens and 296 AST
nodes attained by another program.

FAIR SIZE COMPARISON
===================
Inherited implementation composition: 558 -> 545 bytes.
Adding uniform zero:                   545 -> 550 bytes.
Adding constructed majors:             550 -> 556 bytes.

Thus the new profiles are smaller than the literal supplied minimum,
but the new representation itself costs code under a fully matched
comparison. No simultaneous token/AST/byte record or absolute lower bound
is claimed. Maximum-compression gzip is included only as information.

Across the 16 successful non-neutral comparison examples:
                    Commands    Compact JSON bytes
matched historical       120                 5029
uniform zero              90                 3801
constructed majors        90                 2955
These are selected examples, not universal or representative percentages.
The direct zero computation I(0,0;v.0)=0 changes from 3 packets / 97 bytes
in the specified published repair to 1 packet / 23 bytes.

PROGRAMS
========
code/control_compact.py                 545 bytes; inherited representation
code/control_explicit.py                553 bytes; ordinary list test
code/checker_zero_compact.py             550 bytes; uniform zero
code/checker_zero_explicit.py            558 bytes; ordinary list test
code/checker_constructed_compact.py      556 bytes; constructed majors
code/checker_constructed_explicit.py     564 bytes; ordinary list test
code/checker_readable.py                 1600 normalized / 2192 raw bytes

For review and routine use, start with checker_readable.py or the
constructed explicit-list checker. Each is complete and imports only
Python's standard json module. No producer or reference checker is imported.
Each .py.gz is a level-9 gzip of the complete delivered source.

RUN FROM THIS DIRECTORY
=======================
python3 code/checker_constructed_explicit.py < examples/constructed/zero_base_direct.json
python3 verify.py
python3 measure.py
python3 build.py

Verification reproduces 504 ordinary/optimized-Python expectations and
four deliberate guard-mutation checks. It includes direct computations,
zero-source transport, nested binders, contextual induction, invalid future
parameters, false conclusions, compound-progress rejection, and malformed
inputs. These finite checks are not a proof-assistant formalization.

measure.py charges complete modules, removes genuine docstrings, applies
ast.unparse and a trailing newline, and counts significant tokens, AST nodes,
UTF-8 bytes, raw-source gzip and normalized-source gzip. Runtime versions
and SHA-256 hashes are recorded. It regenerates the report's metrics table.

build.py invokes pdflatex twice. A TeX installation with the packages listed
at the top of report.tex is needed. Reproduction needs no network access.
The tested Python version is 3.12.14. Large valid proofs remain subject to
ordinary interpreter memory and recursion limits.

FORMAT AND SOURCE NOTES
=======================
code/FORMAT.txt specifies the raw interface. The number zero is raw scalar
1 in the new canonical representation, while successor zero is [1].
Instruction markers 0 and [] are not recoded. Local scopes require the
local-scope producers in tests/; old globally numbered certificates are
not silently assumed compatible.

examples/old, examples/zero and examples/constructed contain corresponding
certificates in their own formats. Use the matching checker family.
tests/ contains untrusted named producers and the process-test harness.
evidence/ contains the comparison manifests, validation receipts, metrics,
and review notes. reference/ and appendices/ contain attributed upstream
sources and their license. No upstream repository was changed or published.

FURTHER RESEARCH
================
The paper ends with concrete questions: a cheaper constructed-major
protocol, actual removal of an arithmetic or logical primitive, a fully
charged definitional I0 normalizer, and a compact formal verification of
opening, scope and generated-assumption soundness.
