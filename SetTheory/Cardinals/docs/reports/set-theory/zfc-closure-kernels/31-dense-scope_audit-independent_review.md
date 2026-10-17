# Independent review of the EPSC2 default-index change

Reviewed files: `theory_scope/epsc2_original.py`,
`theory_scope/epsc2_default_indices.py`, the author's finite audit, and
`theory_research_notes.md`. The preserved original is byte-identical to
the EPSC2 checker in the incoming archive. The changed checker audited here
has SHA-256 `10b43c8abbda1e72677a347a54f86ec12da18771a9cbaa5f7e32c30d8a126d52`.

**Outcome: no mathematical or public-checker correctness defect found in
the reviewed change.** The independent executable checks pass. This is an
ordinary proof/source audit, not a proof-assistant certificate or a binary
machine implementation.

## The unbounded argument

For positive current scope d, the normalizer sends each atom index i to
min(i,d-1). It preserves Bottom and implication and uses scope d+1 below a
universal binder. Structural induction proves that every finite raw formula
normalizes to a well-scoped formula, already well-scoped formulas are fixed,
and normalization is idempotent. The quantifier induction must keep d
arbitrary; applying the initial constant d=4 throughout the tree is incorrect.

On a nonempty environment of length d, `select_last` is exactly lookup at
min(i,d-1). It requires neither computing d nor dividing by d; it stops at
the final available entry. A matrix starts with four projected values. Each
of its own quantifiers prepends a value, so matrix environments are always
nonempty and grow by precisely one per binder. This yields the semantic
equivalence between lazy evaluation and materialized normalization N_d.

The whole public search is a presentation of the same ordinary EPSC2 theory.
Every raw matrix F generates an axiom equivalent to the proper instance for
N_4(F), while each old legal matrix is unchanged. No quantifier ranges are
restricted; different environment slots may name the same element.

## The exact code boundary

The public `axiom` path still calls `parse`, which accepts only finite
Bottom/Rel/Imp/All syntax with natural atom labels. It cannot insert a user
template hole, an arbitrary alleged axiom or a supplied target. The emitted
root is always the fixed closed EPSC2 template.

The three actual template projection sites remain exactly
(2,0,4,3), (1,0,4,3), and (0,1,4,3). `Entry.exposed` produces a new
four-entry matrix environment and clears the matrix field. The matrix does
not accidentally inherit all five wrapper slots. Later descendants use
ordinary matrix formulas without holes. Template-owned atoms are already
well-scoped, so changing their lookup to the total helper leaves them
unchanged as well.

The removed eligibility checks concern matrix scope. Proof-reference guards,
rule arities, the primitive Bottom closure test and the fresh-parameter
allocator are unchanged. Syntactic variable payloads are not parameter
names: an out-of-range index only selects an existing environment value and
does not reserve or introduce a fresh eigenparameter.

For a certificate C, replace its matrices by N_4 of those matrices and keep
the exact same proof tree P. An induction on the finite pending-branch
traversal relates the changed checker on C to the original checker on this
normalized certificate. Signs, environment contents, branch lengths,
reference indices and allocator counters are identical. Normalization
preserves every formula constructor. Atom closure sees the same ordered
pair of allocated names; Bottom closure sees the same actual constructor.
Thus acceptance/rejection and all reported traversal metrics agree.

This argument has a useful numerical strengthening: every old accepted
certificate remains accepted by the new checker at the **same natural
candidate code**. Consequently, if any refutation exists, the least new
accepting code is at most the least old accepting code. Running time can
nevertheless increase because previously rejected scope-invalid matrices
now undergo proof traversal. Alias redundancy is therefore a runtime
tradeoff, not a reason that the first accepting numerical index increases.

## Independent targeted evidence

`independent_scope_audit.py` was authored separately from the candidate
patch and does not rely on its own normalizer for the principal witness.
It checks:

* A concrete accepted collision-specialization proof. The raw formula is
  `(forall Rel(0,100)) -> Rel(50,100)` at environment (0,1,2,3).
  Under default semantics it is `(forall x R(x,q)) -> R(q,q)`. A three-action
  tableau deliberately instantiates the universal at the already allocated
  q=3. The same tree is accepted by the original checker on the explicitly
  normalized formula. The original checker rejects the raw unscoped formula.
* Two invalid attempts to identify a fresh witness with q are rejected.
  The tested branch contains T R(q,q) and F forall x R(x,q), which is
  satisfiable. A fresh witness cannot be closed as if it were q, and a
  negative universal cannot use a certificate-selected old value.
* Each real template hole projects exactly four entries; one matrix binder
  then creates five. A huge index with 100,001 bits selects the last actual
  environment entry without introducing a fresh name.
* Five malformed or falsely closing public certificates are rejected,
  including supplied holes, Boolean/negative labels, a fake target field,
  and an attempt to close a generated axiom as positive Bottom.
* Injected MemoryError, RecursionError and OverflowError propagate through
  `accepts_number`. They are neither accepted refutations nor rejected
  candidates that the search could silently skip.

The author's broader finite suite checks additional semantic/projection
cases. Its initial 10,000 candidate prefix contains no formerly unscoped
matrix, so its separate high-code targeted tests matter. The independent
collision witness above is a logical demonstration, not a PSC refutation;
it enters only the generic test interface. The strict public theory entry
cannot receive its negative assumption as an extra axiom.

## Remaining limits

The trusted mathematical object is the ideal finite algorithm. The host
implementation can exhaust resources and is not an unbounded physical
machine. The scalar default lookup does not replace genuine cross-variable
instantiation or eigenvariable freshness. No state saving follows before
the scope-checking and default-lookup alternatives are compiled in the
same backend. These qualifications do not weaken the finite-certificate
transport theorem; they identify its exact endpoint.
