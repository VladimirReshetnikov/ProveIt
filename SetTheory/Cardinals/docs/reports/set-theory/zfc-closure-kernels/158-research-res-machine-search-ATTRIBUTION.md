# Attribution and scope

This packet was prepared for Vladimir Reshetnikov's ProveIt project on
21 October 2026 in a ChatGPT-assisted research session. It reports bounded
searches that did not produce a verified 217-state consistency machine.

The accepted K218 machines, source sites and mathematical calibration are
upstream ProveIt work. The equal-head and shifted-head diagram checkers are
upstream tools, copied with their existing byte pins; the shifted checker's
local import path is the only portability change to that checker. The
upstream attribution and license are retained under `inputs/`.

The new contribution is the compiled all-pairs, fully synthesized two-action
search, its blank-window and observed-interface variants, the wider empirical
context experiment, standalone replay tools, separate accounting checks and
execution evidence. The underlying demand-driven pruning idea comes from
the prior selected-pair K219 search. No claim of originating that idea is
made here.

The finite primitive-interface inputs and tape helpers were shared by the
parallel relay/bootstrap investigation in the same session. Their use here
is explicitly finite candidate discovery, not a substitute for the pinned
unbounded symbolic runtime checker.

New material is supplied under the included MIT No Attribution license,
matching the supplied upstream license. The packet claims neither an
independent human review nor a newly compiled Lean/Rocq theorem. The
standalone Python audits are separate implementations within the same
research session; their precise scope is recorded in their receipts.
