# Mathematical review within this task

The construction was reviewed in separate passes covering the arithmetic
foundation, the continuous laws and limit theorems, the finite Lean kernel,
the density-realization bridge, and the conditioning/process section. This
record describes internal mathematical review, not external peer review or
a completed machine verification of the continuous theory.

## Issues resolved in the final argument

- **Fixed primitive recursive definitions:** the report uses schemas over fixed
  programs and numerical parameters. It explicitly rules out a total universal
  primitive recursive interpreter. The Lean `Eval` graph does not claim such
  an interpreter or its uniform totality.
- **Coherence of random variables:** all names live on the same fair-bit
  cylinder algebra. Laws produced by quadrature are turned into sorted dyadic
  histogram tables using the same uniform source. The finite monotone coupling
  identity proves the Cauchy estimate; unrelated pairwise couplings are not
  substituted for a common joint realization.
- **Heavy tails:** the sampler uses one target clipping radius and a separately
  chosen, possibly much larger quadrature radius. A single shared radius would
  make the desired CDF error budget fail for the Cauchy tail. Downward-rounded
  cell masses and residual mass at zero give the stated uniform moment-tail
  domination.
- **Integrability:** `L0`, `L1`, and `L2` representations are kept distinct. The
  Cauchy identity variable is admitted in `L0`; its symmetric principal value
  is not called an expectation. The clipping inequality supplies the explicit
  Vitali bridge and the bounded-multiplier product argument.
- **Discontinuous observations:** threshold indicators require boundary-band
  certificates. Soft ramps give defined upper-envelope observations when a
  sharp event name is unavailable. No unspecified outer-probability real is
  introduced.
- **Finite calculus:** the fundamental-theorem and substitution steps retain
  increment contracts, local bounds, and decay moduli. Decreasing substitutions
  retain oriented lengths or reverse endpoints. Gaussian normalization has a
  simultaneous explicit cutoff budget, separate from the moment coefficient
  identities already present in ProveIt.
- **Almost-sure language:** the strong-law and Borel--Cantelli conclusions are
  positive event inclusions and small-mass covers in the internal event
  algebra. The report does not identify a constructive negation of convergence
  with a witnessed infinite deviation sequence. The usual pointwise reading
  is stated as external measure semantics.
- **CLT constants:** the quintic cutoff has a globally 60-Lipschitz second
  derivative. Taylor replacement gives the displayed smooth-test error and
  the conservative `delta^(-8)` sample-size bound. A stronger Berry--Esseen
  estimate is not imported from an earlier report without its analytic bridge.
- **Conditioning and stationarity:** the Bayes ratio estimate retains the
  evidence lower bound. Gaussian conditioning divides by a positive marginal
  density, not by a singleton event probability. The AR(1) invariant-law check
  includes both `a*m+b=m` and `a^2*v+sigma^2=v`, and its coupling compares laws
  rather than claiming convergence of the noisy trajectory.
- **Formalization evidence:** the object-language target was compared with
  ProveIt's actual `Prf PRAAx` declaration. Compiled standard-model algebra,
  compiling specification structures, inspected upstream derivations, and
  future continuous embedded proofs remain separately labeled. A declaration
  inventory corrected the named-theorem count to 30; a comment had caused an
  earlier loose text count to report 31.

The explicit proof obligations that remain are recorded in the report's
formalization section, `lean/ROADMAP.md`, and `metadata/theorem_status.json`.
