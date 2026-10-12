# Source audit and attribution boundaries

## Inspected material

The current canonical manuscript README and selected report source passages were
read through the connected GitHub tools. The core immutable reference used for
the anchor definitions is `0dfef47533f8bbf23d12aa4f1894b9bea61f6e0a`.
A later supplementary report was read at
`cc569dca8622dfc8fa02906da37d0a1b8831b5e7`.
These are per-source immutable references, not a claim that every read came from
one atomic checkout.

1. `Analysis/Polylogarithms/docs/manuscript/README.md`: scope and status, including
   the unresolved Gaussian period claims. The inspected README repeats the
   paragraph beginning with the complete 1,032-input first-letter-X family and
   rank 1,008/kernel dimension 24. The proposed editorial change is deletion of
   its second copy, subject to checking the integration baseline.
2. `docs/incoming/README.md` and a partial incoming-directory listing: intake
   conventions and current report names. The binary archives were not exhaustively
   extracted or audited. A partial listing must not be treated as a complete inventory.
3. `Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/quartic-spectral-reconstruction/README.md`
   and selected ranges of `article_singlefile.tex`: quartic moments, Q5/Q7, and
   earlier higher-power research questions.
4. `Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/bernoulli-tails-spectral-faces/README.md`
   and `Bernoulli_Tails_and_Spectral_Faces.tex`, ranges 1-330, 520-770, and 840-1090,
   at `0dfef47533f8bbf23d12aa4f1894b9bea61f6e0a`: all-power and repeated-even-tail
   recurrence, existing finite-cutoff method, J7/K8/K9 definitions, and quintic/sextic
   generators. The existing results retain their source attribution.
5. `Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/lattice-contacts-mixed-zeta/README.md`
   at `cc569dca8622dfc8fa02906da37d0a1b8831b5e7`: the report states a polarized
   recurrence for arbitrary unequal even-order products. Its complete proof was
   not audited in this session; its stated scope is credited as prior work.

Focused searches for the new K8/K9 coefficient combinations did not locate the
same reductions in the returned relevant results. Such searches are not a proof
of absence from the full repository or literature.

## What is not new here

Hurwitz asymptotics, Faulhaber polynomials, Gamma and Stieltjes shift recurrences,
stuffle and shuffle products, MZV duality, and minimum-index ordering of zeta
tails are classical. Hoffman's tail-product method and the Ihara-Kaneko-Zagier
double-shuffle theorem are primary references. The source's all-power even-tail
generators and formal-coordinate ranks are inherited.

## Proposed new integration content

The explicit arithmetic reductions of J7/K8/K9, their short independently
replayed certificates, the arbitrary-integer mixed moment compiler with its
odd-degree W-2 ceiling, the full (2,3) coefficient formula and rational telescoper,
and the combined final-index MZV/polylogarithm realization of Stieltjes and Gamma
transport are proposed additions. Historical priority outside the inspected
sources is not asserted.

## Corrections and non-claims

No mathematical error in the specific precursor formulas used here was found.
The exclusive/inclusive-cutoff distinction in the article is a normalization
warning, not an allegation that the predecessors made that error. An initial
research direction in this session duplicated the newer all-power theorem; the
article corrects that attribution and does not present the duplicate as new.
The README repetition is an editorial correction only.

No Gaussian S6/revised S8 conjecture, unrestricted unequal-tail reconstruction
claim, period independence, or minimal functional depth is established. No remote
repository edits or Lean formalization were performed.
