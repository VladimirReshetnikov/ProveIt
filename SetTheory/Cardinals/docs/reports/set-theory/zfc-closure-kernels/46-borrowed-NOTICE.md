# Attribution and scope

Original research, code, report text, and glue in this package were prepared
by OpenAI's research assistant for Vladimir Reshetnikov and ProveIt. The
independent reviews were separate mathematical and executable checks within
the same research session; they are not external human peer review.

The contribution builds on:

- Mira-Cult's original optimized binary consistency machine and register engine.
- Jeff's upstream formal verification and finite program declarations.
- Andrew James Wade's binary/register compiler framework and generator helpers.
- mira-emmy's public 253-state reduction (PR20, pinned in the report).
- The ProveIt formalization and its 34 reconciled research contributions,
  particularly sources 08, 09, 19, 20, 21, 26, and 34.
- The five additional incoming archives present at the audit cutoff, especially
  the unary support model and binary-Union repair.
- Andrew Pitts's standard nominal-set support calculus.

The countdown itself is a standard algorithm. The new engineering work is
the specified initializer, reuse of future register payload and guarded writer
transitions, cleanup refinements, and measured complete-table composition.
The final shared dispatcher return is source34's earlier idea. Exact state
quotienting is standard and is not a new public253 reduction.

The logical fusion is elementary propositional factoring, applied here to the
complete original emission family. The new theory results are a BU/AU raw
deduction synthesis and the finite-dimensional interpretation application of
bounded support. Novelty is claimed relative to the inspected corpus, not as
an exhaustive worldwide priority claim.

## Retained license boundaries

The unchanged helper files in `code/fusion/vendor/` preserve their original
MIT No Attribution notices and byte identities. `code/fusion/PROVENANCE.md`
identifies every source. The initializer subpackage also retains Wade's
notice and records the provenance of its derived machine tables.

The ProveIt upstream-import README explicitly records the absence of an
upstream-wide license for the pinned Jeff ZF snapshot. The Wade generator
notice is not treated as a blanket grant over all upstream program data.
This package does not relicense that work. Original new material and imported
or derived material remain distinguished by the provenance records.

## Proof boundary

No supplied table is claimed to be a new sub-253 consistency machine. Passing
the finite checks establishes their stated finite properties. It does not
establish a new internal ZFC theorem about their entire unbounded executions.
The report gives the ordinary proofs, inherited calibration, and precise
remaining bridges.
