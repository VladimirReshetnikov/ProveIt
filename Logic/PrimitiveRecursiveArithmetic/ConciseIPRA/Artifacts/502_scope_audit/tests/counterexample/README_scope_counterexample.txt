SCOPE-SCAN COUNTEREXAMPLE
=========================

This folder contains a deliberately UNSOUND checker variant, a small closed
counterexample, and its deterministic generator. The unsound variant is an
experimental negative control, not a proposed proof checker.

Files relevant to the report:
  scope_counterexample.tex        Self-contained LaTeX section (article fragment).
  future_scope_attack.json        Exact 17-packet certificate, 912 UTF-8 bytes.
  make_scope_attack.py            Deterministic certificate generator.
  no_initial_open.py              Deliberately unsound 250-token negative control.
  scope_counterexample_results.json  Reproducible observed results and metrics.

The negative control is the incoming smaller_envelope/checkers/tokens.py
program with exactly one replacement:

  while i(a) not in g:

becomes

  while a not in g:

The original program uses a global, strictly decreasing scope floor. Thus the
counterexample also refutes the proposal that globally fresh parameter names
make the entry scan redundant.

Input protocol
--------------
The input is one JSON array. Its last element is the public goal. The preceding
elements are four-field proof packets [m,s,u,t]. The checker reads by pop(),
so packets execute in reverse array order. The first executed packet is the
penultimate array element. Each packet is one instruction; proving its major
can recursively consume later instructions before the current instruction
allocates its own fresh parameter. An unused prefix is allowed by the frozen
protocol. Normal exit with exactly ACCEPT followed by a newline means accepted;
an exception or any other termination means rejected.

The false goal is the closed guarded formula

  D_{x,y}( I(y,0;u.x) = I(y,0;u.S(x)) ).

Its native array is [[[5,0,7],[5,0,[11]]]]. The ordinary meaning is equivalent
to exists x, x=S(x). The zero row is 0=0 and the row y=1 is x=S(x). Therefore
standard natural numbers falsify it, and iPRA proves its negation.

The certificate is accepted by no_initial_open.py both normally and under
python -O. It is rejected by the unchanged 253-token control and by the proposed
502-byte bytes_eager_selector.py, in both modes. The 502-byte checker uses
local floors; its rejection occurs at the first raw major with floor zero,
before that protocol difference matters. The main counterexample compares
only the exact global-floor control and its one-line modification.
The rejection is a genuine
scope check, not the public-goal grammar: the goal is closed and canonical.

The generator uses no search, external dependencies or network. Running it
recreates exactly the supplied JSON bytes. Read the LaTeX section for the
staged explanation and the exact packet listing.

Earlier fixtures
----------------
Before the new counterexample was constructed, the negative control matched
all 121 applicable JSON fixture outcomes in the incoming smaller_envelope
package. That finite agreement did not justify removing the scope scan.
