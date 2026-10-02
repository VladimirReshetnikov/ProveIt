# Provenance and research status

## Repository review

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected on 2026-10-02. The main-branch head observed through the GitHub connector
was `f1edb38f93aa0a362a34b531a600909f6e74608a`, timestamp
`2026-10-02T18:34:21Z`. Reads of the README and historical audit were made during
the review; this is not a claim that the entire repository was downloaded,
rebuilt, or exhaustively searched.

Relevant reviewed material:

- `Computability/HilbertTenthProblem/README.md`.
- `Computability/HilbertTenthProblem/Papers/1980/REVERSIBLE_FINITE_HISTORY_MODELS.md`,
  blob `cb31d0a108b9a19fc33da6fa89a73b604e15e260`.

The reversible-history audit's important methodological distinction is between
cheap local arithmetic relations and a complete computation certificate with
input, wiring, boundary, and halting semantics. Its historical operation figures
are not used as current facts or as assumptions in this article. The new compiler
has not been merged into or tested against a repository-wide Lean build.

## Literature consulted

- Jérôme Durand-Lose, *Small Turing universal signal machines*, EPTCS 1 (2009),
  70–80, DOI 10.4204/EPTCS.1.7, arXiv:0906.3225. Model definitions and the
  published universality construction were reviewed; relevant PDF diagrams and
  the speed/rule table pages were visually inspected. No complete universal
  rule table was transcribed into this package.
- Florent Becker, Mathieu Chapelle, Jérôme Durand-Lose, Vincent Levorato, Maxime
  Senot, *Abstract Geometrical Computation 8: Small Machines, Accumulations and
  Rationality*, arXiv:1307.6468 (2013). Used to position, not claim priority for,
  the accumulating-clock example.
- Seymour Ginsburg and Edwin H. Spanier, *Semigroups, Presburger formulas, and
  languages*, Pacific J. Math. 16(2) (1966), 285–296. Used for effective
  semilinearity, projection closure, and Presburger decidability.
- Matthias Beck and Sinai Robins, *Computing the Continuous Discretely*, second
  edition (2015), with the author-hosted updated draft. Used for the classical
  rational-polytope Ehrhart theorem.
- Yuri V. Matiyasevich, *Enumerable sets are Diophantine* (1970), and Bayer et al.,
  *Diophantine Equations and the DPRM Theorem*, Archive of Formal Proofs (2022).
  Used only for the classical unbounded Diophantine existence statement.

The exact compiler, examples, matrix exports, and regression tests were developed
for this response. The manuscript is not a claim of peer review or established
historical priority. No referenced papers are redistributed.
