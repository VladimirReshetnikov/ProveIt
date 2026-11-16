LOCAL-TO-GLOBAL CONSTRUCTIONS IN INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
Prepared for Vladimir Reshetnikov — 15 November 2026

START HERE
  ipra_local_global.pdf       Complete human-readable research report.
  report.tex and paper/       Complete LaTeX sources (keep together).
  CLAIMS.json                Exact result-by-result status and boundaries.
  lean/FORMALIZATION.txt     Definitions, proof endpoints, completion order.

MAIN CONTRIBUTIONS
1. An actual kernel-checked Prf PRAAx rule turning local initialization and
   step derivations into correctness of a variable-length PR recursion.
   The state, time and arbitrary numerical parameters are all explicit.
2. A fully written classical-to-intuitionistic transfer argument at the
   same first-order PRA strength, and bounded witness recovery. The Lean
   syntax and translation of every source axiom are checked. The full
   derivation translator and equality-stability adapter remain unimplemented.
3. Uniform local solutions of rational polynomial ODEs as PR rational names,
   with explicit Euler Cauchy bounds, controlled derivative contracts,
   finite-precision uniqueness, and a polynomial conservation compiler.
   Worked applications: Hermite's identity, exponential/oscillator names,
   the circle invariant and the sector-integral accumulator.
4. Explicit integral-point bounds for split polynomial branches, with a
   uniform complete enumeration and exact classification of
        product_(j=1)^m (y - x^j) = 1, m >= 3.
   For m=3 the complete list is (0,1), (1,2).

SOURCE BASELINE
  https://github.com/VladimirReshetnikov/ProveIt
  d56cd5505fb93135b90b048bf3dcca9e73615162
  Targeted comparison with the six existing foundation packets and the
  relevant theorem reports. No blanket verification of all 57 packets.
  Exact source paths and hashes: provenance/source_manifest.json.

FORMAL STATUS
  Lean 4.32.0 compiled seven standalone modules with Std only.
  ObjectIteration.lean and ObjectExample.lean construct embedded Prf PRAAx
  derivations. NegativeSyntax.lean proves syntax and source-axiom translation.
  ODETargets.lean and SplitTargets.lean are executable definitions and
  UNPROVED goal propositions; compiling them does not prove those goals.
  No complete deep application proof is claimed. No sorryAx or
  Classical.choice occurs in the audited proof dependencies. Standard
  propext and Quot.sound appear in the Lean metatheory.
  RepositoryAdapter.lean is source-only and excluded from the standalone build.

REPRODUCE
  python3 build.py checks
  python3 build.py paper
  LEAN_BIN=/absolute/path/to/lean-4.32.0/bin/lean python3 build.py lean
  LEAN_BIN=/absolute/path/to/lean-4.32.0/bin/lean python3 build.py all

  Python 3.10+ and its standard library are sufficient for exact checks.
  The PDF uses standard pdfLaTeX packages (AMS, Latin Modern, geometry,
  microtype, listings, enumitem, booktabs, xurl, hyperref, fancyhdr).
  The PDF script has a private-format fallback for the preparation system;
  it does not use shell escape or modify system TeX configuration.
  The build does not download Lean or other dependencies.

CONTENTS
  paper/       Full proofs, source comparison, induction audit, bibliography.
  lean/        Checked embedded rules, typed targets, integration adapter.
  code/        Two exact-arithmetic reference implementations.
  evidence/    Actual compiler, dependency, source-match, example and PDF QA logs.
  provenance/ Pinned source manifest and audit scope.
  SHA256SUMS   Integrity hashes of archive members other than itself.

LIMITS
  The paper does not prove general Siegel/Faltings, obtain uniform rational
  Mordell-Weil generators, supply missing prime-distribution estimates, or
  choose singular Puiseux branches from arbitrary Cauchy coefficient names.
  The ODE result is unconditional locally for finite rational polynomial
  inputs. Larger horizons require the stated uniform invariant, constructed
  explicitly for the worked systems. Full geometric disk-area normalization
  and the arithmetic transcendence steps remain separate.
  The finite tests are implementation evidence, not universal proofs or an
  iPRA proof checker. No historical priority claim is made for the methods.
