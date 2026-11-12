CHECKERS AND THEIR SCOPE
======================

orbit_checker.py is the independent, explicit-syntax implementation of the
new calculus in the report. native_checker.py implements the adopted NPrf
eight-rule kernel. witness_checker.py implements its existing WPrf variant.
The latter two are new matched controls, not downloaded upstream checkers.
They share the same syntax, substitution helpers, hypothesis discipline,
public-goal validation, error behavior, and file interface with the new
checker. All code is included in each standalone file and counted.

Run, from the package directory:

    python3 code/orbit_checker.py < tests/certificates/identity_at_three_orbit.json
    python3 -B tests/reproduce.py

The first command prints ACCEPT. The second regenerates the main certificates,
runs normal and optimized Python controls, and writes evidence/verification.json
and evidence/checker_metrics.json. Only the Python standard library is needed.

Public interface
----------------

Input is one JSON object with exactly the keys "goal" and "proof". The goal
must be a canonical closed formula. Success means exit status zero and the
single line ACCEPT. An exception or any other outcome is rejection. There is
no imported theory, axiom database, evaluation of supplied code, or external
proof oracle. No Python assert statement is used by any typed checker.

Numerical terms:

    0                         zero
    ["v", k]                  variable with de Bruijn index k
    ["s", t]                  successor
    ["i", n, a, h]            I(n,a;u.h), with u bound only inside h

Formulas:

    ["=", s, t]               equality
    ["q", B]                  Q_y B, with y at index 0 inside B
    ["d", B]                  D_{x,y} B, with y at 0 and x at 1

Each enclosing numerical or formula binder shifts the indices of outer
variables in the usual way. Boolean values are not integers in this syntax.
The scalar numerals 1,2,... in a mathematical display are represented by
successors of 0, not by JSON integer leaves other than 0.

Proof instructions in orbit_checker.py:

    ["hyp", i]
    ["zero", seed, update_body]
    ["succ", counter, seed, update_body]
    ["tr", equation_template, equality_proof, minor_proof]
    ["use", source_argument, seed, closure_proof, minor_proof]
    ["elim", conclusion, paired_proof, continuation_proof]
    ["intro", paired_matrix, witness, premise_proof]

The tr template has one free placeholder in addition to the existing
parameters and must be a literal equation. Compound transport is a derived
rule of the mathematical theory, not a primitive instruction of this checker.

In use, the major proves Q B. Its effective source is the supplied argument
when B is a literal equation, and 0 otherwise. The minor must prove B(source).
The conclusion is B(I(source,seed;u.Su)). No computation conversion is silently
performed: converting I(0,seed;Su) to seed requires a checked computation and
equational transport. This is exercised in identity_at_three_orbit.json.

In elim, the continuation has one fresh parameter and the new first hypothesis
Q B; all previous hypotheses and the declared conclusion are weakened by that
parameter. The checker compares the synthesized continuation conclusion with
the declared conclusion's weakening. A fresh existential witness cannot escape.

In intro, substitute the witness for x in the paired matrix. Introduce a fresh
parameter z. For an equation matrix the first hypothesis is B(witness,z);
for a compound matrix it is B(witness,0). The premise must synthesize exactly
B(witness,Sz). Existing hypotheses are weakened. The witness is checked before
the fresh parameter exists.

Matched old kernels
-------------------

native_checker.py uses ordinary closure elimination

    ["use", target, closure_proof, zero_instance_proof]

Its intro instruction always retains the zero instance. It also has

    ["ind", equation_matrix, progress_premise]

which introduces Q at a literal equation. witness_checker.py uses the old use
instruction and has no ind instruction. Its intro selects progress exactly
when the matrix is an equation and the witness is the literal term 0.

The three systems assign different meanings to atomic Q and D. Therefore
an identical formula need not have the same truth value in all systems. The
old_atomic_case_is_not_progress and boxed_old_atomic_case fixtures deliberately
test this distinction. The equivalence in the report uses formula translations.

The new readable checker is smaller than the matched NPrf implementation but
larger than the matched WPrf implementation. Its measurements must not be
presented as an overall proof-checker minimum.

Ancillary compact profiles
--------------------------

ancillary/checker_tokens.py, checker_ast.py and checker_bytes.py implement the
PREVIOUS guarded-source presentation, not the new progressive orbit calculus.
Their common mathematical consequence relation and public syntax contract are
inherited from the authenticated guarded-source package. The changes compose
an existing neutral-zero premise encoding with tail iteration of a continuation.

The byte and AST profiles replace the initial administrative truth [] by raw
integer 0; neutral packet-major fields are changed accordingly. The token
profile replaces a recursive continuation by a while loop with an immutable
tuple context. Its global-scope certificate language is unchanged. No formula
or numerical axiom is changed by these implementation operations.

The profiles attain, separately, 256 significant tokens, 278 AST nodes and
521 normalized source bytes. Different programs attain these coordinates.
The preceding source package attains 257 / 279 / 522 in the same sense.
This is an implementation composition, not a new arithmetic or logical basis.
These small programs rely on the inherited canonical guarded public-goal
contract and do not themselves validate that public grammar. The main typed
checkers do validate their full public Eq/Q/D grammar. These contracts must
not be mixed when comparing sizes.

tests/ancillary/SOURCE.json records the immutable archive provenance and exact
source hashes. tests/ancillary/reference holds the three comparison files.
The 63 inherited ancillary cases are each checked in normal and -O mode.

Evidence and limits
-------------------

generate_cases.py is an untrusted producer. It compiles named terms by explicit
binder environments and does not import any checker's substitution operations.
Positive examples exercise both computation equations, derived reflexivity,
induction with its hypothesis actually used, zero- and nonzero-source orbit
uses, compound cases, and closure extraction. Rejection controls cover wrong
endpoints, wrong minor premises, witness scope, existential scope, compound
induction, compound primitive transport, malformed input, and negative indices.

open_sequents.json contains two INTERNAL RULE TESTS WITH ASSUMPTIONS. They are
not closed theorem certificates for the public interface. In the first, a
false progressive parity assumption implies 0=1, demonstrating that the new
resource preserves its full progressive strength. In the second, B(y) is a
compound formula equivalent to y=1; allowing its source to be 1 would infer
false B(2) from true premises. The checker correctly requires B(0) and rejects.

Counts cover entire normalized standalone Python modules, including parsing
and public syntax checks where present. Raw and normalized maximum-compression
gzip sizes are reported for information. compressed/ contains reproducible
gzip files of the normalized candidate sources (level 9, mtime 0).

Finite test execution is not a formal proof of universal checker soundness,
completeness, or bi-interpretability. The report supplies written metatheorems;
this package makes no claim of a new Lean or Rocq verification. As usual for
finite Python interpreters, resource limits can reject very large valid finite
certificates. The mathematical recognizer is understood with unbounded finite
resources; no resource failure is counted as successful verification.
