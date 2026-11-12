SMALLER CLAUSE-DISCHARGE CHECKERS FOR iPRA
========================================
Prepared for Vladimir Reshetnikov, November 11, 2026.

START HERE
----------
report.pdf is the complete mathematical paper.
report.tex is its standalone editable LaTeX source, including all foundations
and both unbounded acceptance programs. sections/ contains the editable parts.

RESULT
------
There are two fully specified presentations of full first-order intuitionistic
primitive recursive arithmetic, both equiconsistent and bi-interpretable with
iPRA. Both numerical domains are whole, equality is actual equality, and both
numerical interpretation composites have graph x=y.

1. Recommended when complete proof-checker size is decisive:
   code/checker_explicit.py retains the existing three-family Name calculus
   and uses a smaller complete implementation: 2010 normalized bytes.

2. New mathematical reduction:
   code/checker_deterministic.py replaces the supplied equality proof and
   substitution target in Name by a deterministic inspection of its own
   witness clause: 2058 normalized bytes.

In both, formulas are equations and D(x,y).B, with the ordinary reading
  D(x,y).B := exists x (B(x,0) -> forall y B(x,y)).
Scalar terms are normal forms of x,0,S(t),I(n,a;u.h), for the equations
  I(0,a;u.h)=a,
  I(Sn,a;u.h)=h[I(n,a;u.h)/u].
Full normalization is included in each complete checker.

Contexts contain reusable clauses with zero or one antecedent. The fixed
initial clause is [ ; y.y=y]. The inference families are Use, Intro and
discharge. Every logical and nonlogical primitive, every side condition and
all derived intuitionistic connectives are stated in the paper.

DETERMINISTIC DISCHARGE
-----------------------
After proving D B, open it at fresh b, obtaining
  C_b=[nf(B(b,0)); y.nf(B(b,y))].
If the zero row is literally 0=0 and the first row is literally b=t,
the rule selects t. Otherwise it selects b.
From one branch proof of F under C_b, export nf(F[t/b]), provided the
fresh witness is absent from that result. In the fallback case this is F.
There is no equality subproof or independently supplied target term.

The source must be the fresh witness itself. An older parameter cannot
trigger replacement. The discarded arbitrary-source generalization is not
part of either delivered calculus or checker.

The paper proves exact open-sequent equivalence with the earlier Name
calculus. Ordinary elimination and numerical cases are recovered first,
without transport. A two-row selector/parity packet, credited to the prior
work with its rows swapped, then recovers unrestricted term transport.
Formula transport and both directions of the proof translation follow.

MEASUREMENTS
------------
Complete module                    Bytes  Tokens  AST  Gzip-9
Prior witness discharge            2273     732   813    903
Prior uniform binding              2238     693   764    866
Delivered explicit discharge       2010     636   708    791
Delivered deterministic discharge  2058     653   729    805
Explicit with finite fuel          2139     673   755    839
Deterministic with finite fuel      2187     690   776    853

CPython 3.12.14; remove only the module docstring, ast.unparse, one final LF.
All parsing, validation, scope handling, normalization, substitution, rule
checking and final acceptance are included. Gzip uses level 9 and mtime=0,
and is informational rather than a minimization objective. Raw-source sizes
and hashes are recorded as well. Run python3 measure.py to reproduce.

The explicit implementation saves 263 bytes (11.57%) against its direct
predecessor. The deterministic rule adds 48 bytes, 17 tokens and 21 AST nodes
to the identically implemented explicit rule. The logical premise deletion
and the whole-program implementation savings are separate findings.

Neither delivered checker beats the repository's different 516-byte compact
codec or its 788-byte validated public-goal codec. This package does not
establish an absolute smallest axiomatization or a corpus-wide code minimum.
It gives a new complete equality restriction and smaller fully checked
programs in the stated transparent comparison family.

RUNNING THE CHECKERS
-------------------
The ordinary standalone input is [goal,proof]. Acceptance means exit status
zero and exactly ACCEPT followed by a newline. An exception rejects; no
particular rejection message is promised. Example:

  python3 code/checker_deterministic.py \
    < validation/examples/successor_congruence.json

The bounded interfaces take [goal,proof,fuel] with a nonnegative integer.
The public interface checks closed theorem certificates. Mathematical
equivalence is proved for general open clause sequents; externally supplied
open contexts are not an extra undocumented CLI feature.

The proof examples under validation/examples use deterministic discharge.
The frozen explicit examples under reference/old_name_examples use the old
object wrapper. A producer can convert {"goal":A,"proof":p} to [A,p] without
changing p; verification performs this conversion automatically.

REPRODUCTION
------------
Python checks use only the standard library:

  python3 verify_manifest.py
  python3 reproduce.py

Individual commands:
  python3 validation/verify_translation.py
  python3 validation/run_independent_audit.py code/checker_deterministic.py \
    validation/examples --output validation/independent_results.json
  python3 validation/verify_fuel.py
  python3 measure.py

With a configured TeX Live installation:
  python3 build_pdf.py

Rebuilding can change PDF metadata and regenerated evidence. The manifest
describes the originally delivered package, excluding the manifest itself.

VERIFICATION
------------
The core translation suite passed 16 positive certificates, 16 exact-goal
reverse translations, 22 false/malformed-input rejections and 76 actual CLI
runs across ordinary and optimized Python.

A separate named-variable normalizer and forward replayer, importing no
acceptance-checker helpers, passed all 16 positives, 400 exact normal-form
comparisons, 200 bound-substitution comparisons, 200 formula free-name
substitutions, four independently constructed adversaries and 40 CLI checks.
There were no failures or skipped cases in that audit.

The finite-fuel suite passed 29 examples at exact and one-short budgets,
12 malformed-budget rejections, and 128 CLI runs. These are separate suites,
not a count of that many independent mathematical theorems.

Uniform full normalization is total recursive, not primitive recursive.
The fuel variants provide primitive-recursive bounded certificate predicates
for the same theorems. No uniform normalizer-totality axiom or universal
primitive-recursive evaluator is added to iPRA.

These finite checks support the implementation, not a proof of general
soundness or consistency. The latter claims have written mathematical proofs.
The inherited Lean theorem statements were inspected but not rebuilt here;
there is no new Lean or Rocq verification of the deterministic rule.

FILE MAP
--------
code/          Four complete standalone acceptance modules.
validation/    Proof constructors/translators, two replay implementations,
               substantive theorem fixtures, adversarial inputs, results.
reference/     Attributed frozen comparison sources and Lean statements.
evidence/      Exact measurements, normalized code/gzip, budget results,
               provenance and typesetting checks.
sections/      Editable sections assembled into standalone report.tex.
CLAIMS.json    Machine-readable claims and limitations.
MANIFEST.json  SHA-256 and size of each delivered payload file.

PINNED SOURCE
-------------
https://github.com/VladimirReshetnikov/ProveIt
Commit: ffa94f76bc01d1c77168f035caed949179859115
Root: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
The comparison includes all six incoming archives in that snapshot.
See reference/ATTRIBUTION.txt and evidence/source_provenance.json.
Inherited and new materials are available under the included MIT-0 license.
