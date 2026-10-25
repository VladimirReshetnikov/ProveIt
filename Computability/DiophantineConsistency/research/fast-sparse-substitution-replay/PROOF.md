# An exact accumulator substitution for a separate verification replay

This is CODE ONLY / HOLD. No new module, helper, verifier, compiler or benchmark
has been imported, compiled or run. The old centering folder and all parents
are immutable inputs. Its outside observation record is not an accepted final
endpoint manifest. The original fresh optimized process returned143 without
a report or diagnostic; its interruption cause remains unestablished. A later
overlay run cannot change that historical outcome.

## 1. Exact algebraic contract

Represent an integer polynomial by a finite dictionary. A key m is a sorted
tuple of nonnegative variable indices, with repetitions denoting powers; its
value p[m] is a nonzero integer. The empty tuple denotes1. The zero polynomial
is the empty dictionary. Neither dictionary insertion order nor a globally
sorted sequence of keys is part of this mathematical representation.

For canonical integer polynomials p,r and an index i>=0, the old function is:

    d={}
    for m,c in p.items():
        a=con(c)
        for j in m: a=mul(a,r if j==i else v(j))
        d=add(d,a)
    return d

The helper retains exactly the same con, mul, v calls, the same nesting and
the same choice of r. Only the last addition changes. For each expanded a,
it adds every coefficient into one fresh local dictionary, retaining any
intermediate zero. After all a have been processed it removes zero values.
It neither skips unchanged monomials nor changes multiplication, scalar
arithmetic, canonical monomials, the replacement polynomial or its degree.

For each input monomial m, both implementations compute the same polynomial

    a_m = p[m] * product_(j occurring in m) (r if j=i else x_j).

For any output monomial n, the old implementation's final coefficient is
the finite sum of a_m[n] over m, with absent coefficients read as0. Removing
a zero intermediate coefficient does not affect any later sum. The new
implementation computes that identical finite integer sum directly. Integer
addition is associative and commutative and has no overflow here; filtering
zero values once at the end therefore returns exactly the same polynomial.
This proves equality for arbitrary finite canonical integer inputs, with no
degree or support bound and without reference to the centering fixtures.

The adopted con and v functions make fresh dictionaries. The adopted mul
builds a fresh coefficient dictionary and sorts each concatenated monomial
tuple. The helper reads p,r and these temporary a values but writes only its
own accumulator and final result. Thus it never changes either input and
returns a fresh dictionary, including when p is empty, i is absent, r is
zero, p is r, or r itself contains i. In the last case replacement is the
same one-level polynomial substitution as the original, not recursive
re-expansion of the new occurrences of i.

Cancellation can change insertion order. The old add prunes a key at zero
and reinserts it if a later a revives it; the new accumulator retains its
original slot. No claim of dictionary iteration-order equality is made.
The extensional dictionaries and their sorted A.terms lists are equal.

## 2. Why the current verifier preserves its complete checks and report

The original check.py is loaded unchanged only after authenticating its
entire observed34-file tree, every new held core file, and every member of
all three complete sealed parents. It performs its own old authentication
again when its literal main function runs. No producer or optimizer is
imported and no parent CLI entry point is called.

Original main calls support() to load the adopted407-line algebra module.
Patching an earlier, discarded support() result would have no effect.
The wrapper therefore installs an explicit one-call loader adapter: call
the original support(), replace only the returned module's sub attribute,
and return that very module to the unchanged old main. Every other vendor
attribute is checked by object identity against its pre-patch value. The
support adapter and argv are restored even if old main raises an exception.
This adapter is plumbing; it does not replace an old verification check.

The entire old main is invoked. Its original inventory/canonical-JSON/index
checks, policy derivation, both profile verifications, all64 actual negative
and four valid algebraic controls, both signed fixtures per profile, all
forward row translations, complete reverse quartic substitutions and the
whole degree/liveness/census/source/endpoint/map comparisons still run.
Nothing is replaced by a sampled arithmetic test or a cached PASS record.

The actual consumers require extensional polynomial equality: translated
rows are serialized by sorted A.terms; reverse and leading forms use dict
equality; degrees, counts, extrema and exact signed evaluations depend on
the coefficients, not their insertion order. Used-coordinate lists are
sorted. The mixed-monomial corruption is selected by A.norm of the fixed
serialized input polynomial, not an accumulator's output order. The old
error paths and its ordered list of controls remain unchanged.

As a separate required check, original main's entire printed byte string
and newly written external original receipt must both equal the preserved
mode-specific CHECK.json or CHECK_OPTIMIZED.json, including every field,
old source-pins hash, optimize flag, indentation, sorted JSON keys and final
newline. The wrapper also checks that exact serialization. It does not
construct a substitute old report from the expected receipt. The outer
report nests the report actually produced by original main, then adds
explicit overlay provenance and small differential-control evidence.

## 3. Differential controls and their limits

Twelve handwritten small cases compare the helper with the literal saved
old sub and explicit expected coefficients. They cover empty/constant
polynomials, an absent index, unit and zero replacements, a negative
constant, square cancellation, an r containing i, quartic mixed terms,
a nonlinear replacement, cancel-then-reappear, and p/r aliasing.
Each checks exact dictionaries and sorted terms, input contents and order
unchanged, canonical nonzero integer results, and a fresh independent
result. The cancel-then-reappear case deliberately observes different
iteration orders while requiring equal polynomials. These controls support
implementation binding; Section1 is the universal equality proof.

## 4. Authentication, writes and inherited mathematical scope

SOURCE_PINS includes the outside root observation JSON/Markdown, all34 old
files, every payload and manifest of the three sealed parents, and four
new core files. The runtime recomputes exact complete member sets, hashes
and byte counts, including every old data file, old receipt/stdout pair,
held file and vendor. Both string and typed parent-manifest records are
checked according to their actual schemas. The old folder must have no
final MANIFEST. The overlay's closed held payload inventory is checked
before either new helper or old checker is imported and again after the
full replay. No Python AST, source compiler or arithmetic benchmark is used.

Both output paths must be distinct ordinary paths outside the whole
repository, without symlink components. The old main retains its own
safe-receipt and identical-overwrite checks. The wrapper likewise refuses
to overwrite a changed outer report. Its temporary stdout buffer holds
only the old report; stdout contains the complete outer report. The held
overlay folder remains unchanged, with all outputs and future replay or
acceptance metadata outside it. No data, certificate or tuple is generated.

The whole old proof/calibration contract is retained exactly: fixed integer
translation, accepted raw monic/free/Horn witness maps, then the accepted
source theorem. No fresh transitive native/compiler replay or stronger
calibration is claimed. No old interrupted run is retried or relabeled.
Any future normal/optimized PASS belongs to this separate overlay program,
and endpoint acceptance remains ROOT's independent decision after replays.
