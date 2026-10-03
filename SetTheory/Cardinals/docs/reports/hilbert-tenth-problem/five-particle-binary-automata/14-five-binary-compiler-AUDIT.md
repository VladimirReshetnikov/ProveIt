# Independent audit of the binary five-particle compiler

## Verdict and scope

The component compiler and its fixed-horizon sum-of-squares frontend pass this
independent mathematical and executable audit. The source-universality review
is separately attributed below. No defect was found in component parsing,
bounded writes, binary numerical conservation, radius, valid-orbit simulation,
exact clocks, or halt observation. This is a human-readable proof audit with
finite regression evidence, not a proof-assistant certificate.

The paid nonnegative-real frontend also passes: it requires one additional
selector-norm residual per source step. Without that payment, the natural-domain
polynomial need not have the same fibers over the real orthant. The audit includes
an explicit rational false-halt witness for that unpaid relaxation and checks
that the paid version excludes it.

This audit does not independently establish the universality of the imported
8408-row source. It verifies the binary compilation theorem for any valid finite
source and tests every imported control at its geometric phase boundaries. The
primary-source finite-input universality claim and original source simulator
are separate provenance obligations; neither follows from the table's size.
A separate lead review has now supplied a passing primary-source receipt: all
30 Table 16 entries were independently transcribed and matched to the pinned
TM table; the finite input encoding was checked; and both register-simulation
proofs were read. The displayed halting configuration underlines b, agreeing
with Table 16's undefined u10,b entry. Only the final prose says c, so the
discrepancy is preserved as a prose inconsistency rather than an unresolved
choice of source machine. No author-issued erratum is claimed. The primary
reference is Neary and Woods, Four Small Universal Turing Machines, Fundamenta
Informaticae 91 (2009), 105–126, DOI 10.3233/FI-2009-0008.

## Compiler proof review

### Full-shift rule and conservation

A component is defined by adjacent occupied-site gaps at most K. Components of
size other than two or three are fixed, including infinite components. For a
three-site component, a unique gap at most D and a remaining gap at least
C=D+1 select a unique packet and marker. H/O/I packet gaps are disjoint. Ahead
and behind are disjoint cases; the two contextual zero-test alternatives inspect
the same old configuration and have complementary guards. No priority convention
or promise about well-formed global inputs is needed.

Every listed output has the same number of distinct particles as its input.
The marker-to-output-packet distance is C>D, and its internal packet gap is
positive, including endpoint decrements. Every output lies in its old component
hull enlarged by E=2D+2. Different components have gap greater than
K=4D+5=2E+1, so these enlarged hulls are disjoint. Consequently separate rewrites
cannot collide with one another or with retained particles. Read-only contextual
bits cannot impair this counting argument, even for false heads and false zero
sensors. The rule therefore conserves every finite-support binary input.

A stronger full-shift interpretation is available: match old and new particles
in sorted order inside each changed component and use the identity elsewhere.
This is a translation-equivariant particle bijection of displacement at most
2K+E. It also preserves the number of particles per spatial period on periodic
inputs and is meaningful for arbitrary infinite inputs.

### Radius, including truncated large components

If a component contributes an output at i, its old hull has distance at most E
from i. A potentially changed component has at most three sites and diameter
at most 2K. Thus all its sites are within E+2K, its K-wide component-boundary
guards are within E+3K, and its possible marker-offset zero read is within
E+2K+Z. The stated radius R=E+3K+Z exceeds all of these distances.

A genuinely large component containing i has a four-site connected witness
within 3K of i and is fixed. A purported small component in the truncated word
that could write at i has all of its boundary guards inside the word; it therefore
cannot be a spurious truncated fragment of a larger true component. Components
close to the window boundary cannot write at i. This supplies the converse
needed to identify BinaryCA.local with the full-shift component rule, not just
a one-way support bound. The radius algebra R=30D+37 is correct.

### Every valid input and every intermediate phase

The three marker positions have separation at least Z, including decrement
1 to 0. The packet has internal gap at most D and cannot simultaneously join
two markers, because Z=4K>2K+D. Only one close pair exists at every intermediate
time. The home zero bit is occupied exactly when the chosen natural counter is
zero; none of the other four particles can spoof it on a valid orbit.

For selected old counter c, side s, and Delta equal to +1 or -1, set

    t_out = Z+c-C-d(O_q)-K
    t_in  = Z+c+Delta-C-d(I_q)-K.

Both are strictly positive. Dispatch is at time 1, endpoint reversal at
2+t_out, and home commit at 3+t_out+t_in. The explicit analytical microstates
used in audit_independent.py agree with the CA step at every tested microtime.
Their total gives the claimed affine clock, including both directions and
minimum-counter cases. Zero SUB and NOP take exactly one step. Halt is fixed.

The three-one halt word cannot arise early on a valid orbit. Its unique short
gap is the H_halt code, distinct from every travel and other home code; the
remote markers are outside its window. Tests check possible anchors at all
occupied sites, which is stronger than checking only the origin. A packet whose
next source state will be halt does not exhibit the word before its home commit.

## Frontend proof review

For a syntactically fixed horizon h and fixed natural starting counters/control,
the emitted natural-domain polynomial is the sum of the squares of its explicitly
listed residuals. Natural selectors summing to one are one-hot. State balance
picks the current control, the zero guards enforce the zero branch, and
nonnegative postcounters exclude DEC at zero. Counter recurrences then force
all subsequent values. Because halt has no outgoing branch, the terminal
condition means first source halt exactly at h. The complete witness fiber is
empty or a singleton, including the optional exact physical clock.

For the paid nonnegative-real variant, add sum_j e_tj^2-1 at each step. On the
nonnegative simplex, every selector is in [0,1], and

    sum_j e_tj(1-e_tj) = 1-1 = 0.

Each summand is nonnegative, so every selector is zero or one. With fixed natural
inputs, deterministic counter updates force integer counters and the exact
clock as well. This proves the same empty/singleton fiber over the entire
nonnegative-real witness orthant. No strict-positive-interior claim follows or
is made. It is not a statement for arbitrary nonnatural external counter inputs.

For h>=1, B branches and z zero branches, the exact unsimplified slots are:

- Natural version: h(B+2) witnesses and h(4+z)+1 squared residuals
- Paid real version: the same witnesses and h(5+z)+1 squared residuals
- Optional clock: one additional witness and one additional residual
- Degree at most four in either version

The sparse emitter counts collected residual monomials and separately reports
sum of squared residual lengths as an expanded ordered-term occurrence bound.
It does not conceal the cost of squaring. Actual collected counts may decrease
when constants or zero coefficients specialize away.

Two documentation qualifications identified by the audit were incorporated:

1. The implemented emitter specializes initial counters and control to constants;
   the symbolic-input formula is stated separately. Substituting a0=x+1 expands
   first-step zero guards and must be re-costed rather than silently inheriting
   the atomic-input monomial bound
2. The emitted h=0 clock version has one Theta witness constrained to zero and
   two residual slots; substituting that known zero can eliminate the witness

There is a separate polynomial for each fixed h. The construction does not turn
h into an unbounded input of one fixed finite polynomial, does not turn a unary
geometric encoding into a free resource, and does not establish an unbounded
single-fold representation theorem.

## Independent executable evidence

All scripts use only local code and Python's standard library. Compiler and
frontend hashes are pinned in their JSON receipts.

- audit_independent.py / audit_independent.json: 450 complete source macros,
  52,885 analytical intermediate states, 238,835 local center checks, 9,907 finite
  conservation cases, 9,520 translation checks, 1,190 exhaustive pair/triple
  shapes with sensor variants, 4,096 exhaustive dense words, 51 long connected
  boundary phases, 1,000 adversarial multiple-component cases, and 288 periodic
  words
- audit_literal_boundaries.py / audit_literal_boundaries.json: all 8,408 literal
  controls, 16,816 counter-zero/one cases, and 205,004 phase-boundary transitions
  using the pinned bundled source. These include initial dispatch, separation,
  target contact, reversal, return separation and home commit
- audit_frontend_independent.py / audit_frontend_independent.json: 2,016 fixed-input
  frontends, 27,504 one-hot branch sequences, 888 rational-coordinate mutations,
  and 4,998 rational simplex points; exact Fraction arithmetic is used

The unpaid fractional counterexample starts at looping control b in a source
with a:ADD0 HALT, b:ADD0 b, c:ADD0 HALT. At h=1, half-selecting a and c matches
b's intermediate numerical control code and invents a halt while the genuine
source never halts. All unpaid residuals vanish; the added norm residual is
-1/2, giving paid SOS value 1/4. Thus the extra real-domain residual is essential
rather than decorative.

## Reproduction

From this directory, run:

    python audit_independent.py
    python audit_literal_boundaries.py
    python audit_frontend_independent.py

Finite checks supplement the all-input arguments above; they are not being
substituted for them.

## Final API-boundary hardening audit

The valid-input construction and its mathematical bounds are unchanged. Before
sealing, a separate implementation-boundary audit checked strict source schema
validation, exact natural counters, exact integer lattice coordinates, immutable
compiler snapshots, and frontend input types. Boolean values are rejected as
counter indices and counters. NOP rows must have exactly two entries. Counter
validation occurs before HALT and zero-horizon shortcuts. Occupancy is validated
before set conversion, so Boolean/float entries cannot hide by comparing equal
to integers; duplicate iterable coordinates are explicitly rejected. Negative
integer lattice coordinates remain valid.

Machine rows are immutable copies of the caller's source lists and mapping.
Compiled CA and frontend structures use immutable tuples/mappings and reject
ordinary attribute replacement and deletion; slots remove mutable instance
dictionaries. The audit identified and closed an intermediate deletion escape
that could otherwise remove the frozen flag. These are conventional Python API
guards, not a security claim against deliberate low-level reflection.

The exact evaluator for the nonnegative-real polynomial accepts nonnegative
integer and Fraction samples. It rejects floating-point, nonfinite, Boolean
and non-real sample values. This exact-sampling API does not change the proved
mathematical statement for the entire nonnegative-real orthant.

The optimization-safe API suite passes both normal Python and python -O:
904 invalid calls are rejected, 24 mutation/deletion attempts are rejected,
source and frontend input snapshots are isolated, and 36 valid macros covering
2,964 microsteps plus 16 valid frontends remain correct. Receipts are
audit_api_normal.json and audit_api_optimized.json; the test source is
audit_api_independent.py.

The three original independent regression suites are also rerun against both
normal and optimized compiler/frontend imports by audit_regression_modes.py.
The harness deliberately compiles each audit entry point with optimize=0,
retaining its checks while testing compiler imports under actual -O. The
combined receipt is audit_regression_modes.json.

Final code hashes:

- five_binary.py: 9022006a4669c7c637ac337a89ea792c55612c23a92c7bedda34af9c9707d90f
- frontend.py: 4d5b3ce9facb439d60a152890b3910c021b242996fbecbeefef7e4c0ba793ca5
