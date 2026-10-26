# Independent mathematical review of Round23 height-one normalization

Separate intake/audit task,26 October2026. AI-assisted internal review, not external refereeing. The reviewed snapshot is the worker's frozen `height_one/` with its selected15 endpoints.

## Verdict

The new source-product fusion/dependency pruning, additive constant inlining, and rare scale expansion in PROOF.md§§1.4–1.7 preserve integer and real zero sets by the stated canonical projection/restoration maps. No division, positivity convention on independent inputs, or nonunit pivot is introduced. The inherited incidence/equality/unit construction transfers those normalized zero sets as stated. No mathematical gap was found.

## Points specifically checked

* Every fused source occurrence is still a signed monomial of degree at most2 and has its exact original pullback only after constructor values are inserted. The proof does not falsely assert equality away from constructor zeros.
* Dead-constructor removal preserves dependency closure and inherited triangular order. Remaining constructors uniquely extend every original tuple; omitted constants/scales have unique intended values and restore all deleted rows.
* Additive inlining uses earlier constants, with K1=1 merely notation. Repeated factors are expanded as repeated occurrences, including all four terms of a square. Collected coefficients need not be±1 at this intermediate stage.
* Replacing a rare scale by c copies of its original coordinate preserves its polynomial c*x on unrestricted real/integer inputs, including zero and negative x. Remaining defining pivots remain monic and acyclic. Final height1 is an independently checked collected-coefficient property, not inferred from signed occurrence notation.
* Incidence energy, cyclic equality penalties, quartic two-alias penalties and the anchored unit path are globally nonnegative. Thus a zero forces every required equality and unit condition before the source residuals are decoded.
* Unit-product dummy elimination and internal tree-edge contraction have the stated unique inverses; the latter's off-zero substitution identity is distinct from merely preserving zeros.
* The universal lift includes the hub cross term: P(L(x))=[sum Rj(x)^2+(sum delta_jRj(x))^2]/2. Omitting that term would be incorrect. Tree elimination gives unique integral flows and the source projection/lift bijection.

The full graph semantic checker is inherited unchanged and independently replays all source/constructor pullbacks and the symbolic lift; this review did not reimplement that entire checker. It separately parsed all15 final coefficient arrays, rejected duplicate monomials, counted coordinates/support/degree, and confirmed exact coefficient set{-1,+1}, constant1 and participation of every variable. Results are in HEIGHT_ONE_LITERAL_METRICS.json. This parsing/recount is not mislabeled an independent graph reconstruction.

The minimum selected endpoint is484 variables/24131terms; balanced531/12020 and533/11985 are distinct tradeoffs. All are exact quartics on unrestricted integers. The proof claims only the enumerated comparisons and named inherited consistency calibration, not a global minimum or new compiled foundational proof.
