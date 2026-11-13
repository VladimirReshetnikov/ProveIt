COMPUTATIONAL EQUALITY: SIX RULES FOR IPRA
Prepared for Vladimir Reshetnikov, November 11, 2026

Main result
-----------
The original raw seven-rule witness calculus is replaced by six rules:
Hyp, Refl, Eval, QE, DE, DI. The numerical terms and Eq/Q/D formulas are
unchanged. There is no canonicalization or normalization during substitution.

Eval combines equality with one computation. Given s=t and b=r, it returns
r=Phi(s,t,b), with exactly these three cases:
  b is s:                         Phi=t;
  b is I(0,a;u.h), s is a:         Phi=t;
  b is I(Sn,a;u.h), s is I(n,a;h): Phi=h[t/u].
All comparisons are syntactic, and h[t/u] is capture-free.

Both computation axioms become three-node derived proofs. A one-iteration
construction recovers arbitrary numerical congruence without induction.
Exact open-sequent equivalence transfers the inherited whole-domain,
actual-equality bi-interpretation with full first-order iPRA, including
both formula composites and the numerical identity graphs x=y.

Files
-----
report.tex / report.pdf          Complete paper and compiled version.
code/checker.py                  Complete selected standalone checker.
code/control.py                  Complete matched seven-rule control.
code/*.normalized.py[.gz]        Normalized source and reproducible gzip-9.
code/translate.py                Untrusted, checked proof translations.
code/verify.py                   Reproduces measurements and finite checks.
code/adversarial.py              Independent adversarial suite (51 cases).
code/examples/                  Translated certificates ready to check.
reference/                      Attributed pinned statements and baselines.
evidence/                       Metrics, verification, provenance, reviews.
CLAIMS.json                     Explicit results and nonclaims.
MANIFEST.sha256                  Checksums of delivered files.

Reproduce
---------
Use Python 3.12 or later (the reported run used 3.12.14), and a LaTeX
installation with the packages named in report.tex. No Python package
outside the standard library is needed for checking or reproduction.

    python3 code/verify.py
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

Example:
    python3 code/checker.py < code/examples/root_reflexivity_zero.json

The certificate is a JSON object with exactly four keys:
variables, context, goal, proof. A successful command prints ACCEPT and
exits with status zero. Rejection is a nonzero exit; diagnostic wording
is not part of the theorem interface. The checker supports open sequents.
Variable zero is the nearest de Bruijn binder. In D, zero is y and one is x.

Boundaries
----------
This is a written universal equivalence proof with executable translators,
finite regression checks, and an inherited Lean interpretation theorem.
It is not a new Lean or Rocq formalization of the new calculus or Python
checker. The included Lean files are reference extracts, not a standalone
Lean build project. The upstream project was inspected but not rebuilt.

The new calculus is a strict local simplification of the raw witness basis.
Complete matched module measurements improve from 3121 to 3039 normalized
bytes, 1008 to 959 significant tokens, and 1064 to 1026 AST nodes. Gzip-9
increases from 957 to 966 bytes and is included for information only.
No absolute simplest-theory result or new 516-byte compact-codec record
is claimed. Six-rule presentations in changed term languages already exist.

The new Eval rule is strictly stable under raw numerical substitution.
The inherited witness-sensitive DI still has its known mode-change issue;
whole-calculus substitution admissibility follows through native equivalence.

Baseline
--------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 11be5aabc6b07262046e2553419bc6b05271d178
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
The six incoming archives present at that commit were inspected.
Exact file and archive provenance is in evidence/provenance.json.

License
-------
The reference ProveIt material uses the MIT No Attribution License,
reproduced in reference/PROVEIT_LICENSE. New code and report material in
this package are provided under the same license.
