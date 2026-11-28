# Reading guide

Names below omit the prefix `New.`. Throughout, `P : Parameters` and `D : Data P`. So `D.targetForms` is the space of target forms of the data `D`.

## 1. Where to start

To trust the result, read `Statements.lean`, the five statements of `Main.lean` and the list of axioms that `#print axioms` gives. All other definitions occur only inside the proof. The rest of this guide is for reading the proof.

`Statements.lean` states the theorems in Mathlib's terms. `Main.lean` derives them from `grh` (no Dirichlet L-function vanishes in re s > 1/2, the pole excepted), with the two lemmas of `New/Main`. First read the files that fix the data: `New/Reduction/Data/FieldsAndPlaces`, `New/Reduction/Data/AdmissibleData` (a table near its top translates letters into names), `New/Reduction/Data/LevelAndTwists` and `New/Reduction/Data/Sizes`. Then read `New/Reduction/Lattices/Heights` for heights, `New/Reduction/Lattices/TwistedLattice` for index and covolume, `New/Reduction/PrimeSums` and `New/Reduction/IntegralTargetForms` for the quantities compared, `New/Reduction/ShortAndEnough` for Theorems A and B (named below), `New/Determinant/Twist/LongForms` for Theorem C, and `New/Reduction/MainInequality`. Its head lists the inputs, what cancels and the errors. `New/Reduction/OneSidedBound` ends with `grh`.

The spaces and maps, with ranks (words and letters: sections 2 and 3): source forms on X₀ (k) go by the Poincaré series to forms of principal level on Y₀ (r), which `D.e₀` projects to the target forms, and from Y₀ by m lifts to Y_m (r + mt). Source forms also go by m lifts to X_m (r + mt + 1) and by restriction to Y_m. The single lifts are W_j (r) → V_j (r + t).

The three main theorems are A, short forms (`D.span_short_integralRamified_eq_top`, `D.indexLe_normalizedPoincare`), B, enough forms (`D.enough_forms`), and C, integral forms are long (`D.integral_forms_long`). The main inequality `star_inequality` combines them. The first table of `INDEX.md` says each in a line.

`New/UpperBound/Objects/LabelsAndIndexTypes`, `New/UpperBound/Objects/Rows` (target forms), `New/UpperBound/Objects/Columns` (source forms, chain data, composite lift), `New/UpperBound/Objects/RowChain` (the chain Y₀ → Y_m) and `New/UpperBound/Objects/PoincareMap` define the main objects. Ramified source forms, local prime sums, gains and exceptional primes are in `New/UpperBound/Size/ShortColumns`. `New/Determinant/Chain/NormOfChain` defines the two determinants. `New/Determinant/Twist/FitTwists` defines regular families of twists.

The folders of `New` follow the order of the argument. The background results that it uses are in `Lib`. Folders are not layers: files of different folders import each other in both directions. `CONTENTS.md` lists every file with its title.

| Topic | Folder | Subfolders and files, in order |
|---|---|---|
| The theorem and its reduction | `New/Reduction` | From a one-sided bound to the zeros (`Zeros`); Lattices, colength and heights (`Lattices`); The data (`Data`); Three theorems and the main inequality (`PrimeSums`, `IntegralTargetForms`, `ShortAndEnough`, `MainInequality`, `OneSidedBound`) |
| Derivatives of theta functions | `New/Derivatives` | Derivatives that count primes (`Divisibility`); The field and its characters (`Field`); The formal group and the exponential factor (`FormalGroup`); The integral vacuum (`Vacuum`); The bound is attained (`Sharpness`) |
| Upper bound: a composite lift | `New/UpperBound` | Theta kernels between definite spaces (`Kernels`); Source forms, target forms and chains of lifts (`Objects`); The seesaw identity (`Seesaw`); Divisibility of the composite lift (`Divisibility`); Size of the composite lift; short source forms (`Size`); Elementary divisors of a Hecke operator (`ElementaryDivisors`) |
| Spanning: a second moment | `New/Spanning` | The second moment and the spanning theorem (`SecondMoment`); Equality of multiplicities (`Multiplicities`); Measures and Bessel functions (`Bessel`); Unfolding, and the proof of the moments (`Unfolding`); The remaining terms (`RemainingTerms`); The main term (`MainTerm`); Two frames at one place (`Frames`) |
| Lower bound: the determinant | `New/Determinant` | A twist for each prime (`Twist`); Norms of theta lifts (`Norms`); The exchange identity (`Exchange`); The norm of a chain of lifts (`Chain`); Auxiliary forms (`AuxiliaryForms`) |
| Lower bound: one lift | `New/OneLift` | One lift and Hecke values (`TestedForms`, `LiftVolumeHeight`); The comparison operator (`ComparisonOperator`); Periods of false lifts (`FalseLifts`); Hecke L-values as squared norms, and their valuations (`HeckeValues`) |
| Lower bound: congruences | `New/Congruences` | Congruences and the choice of twists (`FitTwistsExist`); Congruences and Galois representations (`GaloisRepresentations`); Congruences to first order (`FirstOrder`); Anticyclotomic twists with small Selmer groups (`Selmer`); The local loss (`LocalLoss`); Lifting crystalline extension classes in large weight (`Lifting`) |
| Supplement | `New/Appendix` | Discrete series with a large gap (`DiscreteSeries`) |

`Lib` proves parts of several standard theories, often in a weaker form that suffices here and with its own definitions. For example, Galois representations match the Hecke polynomials for most Frobenii only, up to each η > 0 (`GaloisRep.Attached`), local polynomials only kill and need not be characteristic, and no Weil–Deligne representation is built. Each has an overview in the head of the file that holds the theorem named here: class field theory and duality, `artin_reciprocity`; ℓ-adic and Hodge cohomology, `Variety.ellAdicCohom.woods_hole`; odd classes over cyclotomic fields, `exists_length_shaOdd_le`; Galois representations of eigenforms, `GaloisRep.sphericalCompat_std`; p-adic comparison, `Variety.ellAdicCohom.isCrystalline_and_linearFrob_rel`; p-adic Hodge theory, `GaloisRep.local_clauses_of_trace_limit`; Kisin modules, `Lift.KummerChart.JumpLattice.frame_theorem`; Shimura varieties, `Variety.Model.exists_galois_rep`. Other inputs: the Siegel–Weil and Rallis formulas in `Lib/SiegelWeil`, a simple trace formula in `Lib/Adelic/TraceFormula`, a Chowla–Selberg formula in `Lib/CM/ChowlaSelberg`, primes in progressions in `Lib/Analytic/PrimeNumberTheorem`, and the choice of d, a zero-density count from Pólya–Vinogradov, in `Lib/Analytic/QuadraticTwist`.

## 2. Glossary

The parameters are a multiple q₀ of 18480 and a prime d ≡ q₀/2 − 1 mod q₀. E = `D.E` is K(ζ) with K = ℚ(√−d) and ζ of order q₁; χ_K is the quadratic character of K. X_j (rank `D.n j`) and V_j (rank r + t) are definite hermitian spaces over E. Y_j = `D.spaceY j` has rank r + jt. W_j = `D.spaceW j` has rank r and m − j minus signs. It differs from Y₀ only in the signs at the real places, and each eigensystem of the Hecke operators at split places away from M has the same multiplicity in the good forms on both (`D.finrank_goodForms_inf_eigenPart_eq`). Y_m ⊂ X_m is definite, of rank n_m − 1.

| Word | Lean | Meaning, standard counterpart |
|---|---|---|
| a-place | `D.aPlaces` | infinite place of E, read in (ℤ/q₁)ˣ, that is ≡ 1 mod q₀ |
| b-place, weight | `D.bPlaces`, `D.weight` | b-places are ≡ −1 mod q₀, form a sparse set (`Parameters.IsSparse`, built after Behrend: for primes ℓ ≤ kt and 0 < i < j < l₀, no σ, ±ℓ^i σ, ±ℓ^j σ all lie in it, modulo the part of q₁ prime to ℓ) and have weight b = a/x; all other places have weight a/x₁ |
| chosen place | `D.IsChosen` | prime dividing `D.piM`, half of those above M = p₀p₁ |
| twist | `D.Twist`, `D.MFoldTwist` | automorphic character of U(1) of weight 0 (anticyclotomic), tamely ramified on a set `Q` of places prime to MN that is disjoint from its conjugate; m-fold if its first m powers still ramify at every place of `Q` |
| height bound | `HeightLe` | a family y with one number for each ι : ℂ ≃ ℚ̄_ℓ (`PrimePadicIso`) has height at most c if some H ≠ 0, α and h_ℓ ≥ 0 have log ‖σH‖ ≤ α for all automorphisms σ of ℂ, ‖ι(H·y_ι)‖ ≤ ℓ^(h_ℓ) for all ι, and α + ∑ h_ℓ log ℓ ≤ c. Heights add in products and may be negative; for the constant family 1 the product formula gives c ≥ 0 (`HeightLe.nonneg_of_one`) |
| twisted lattice | `TwistedLattice`, `D.targetLattice` | maps from one space to inner product spaces with integral vectors, one map for each twist; the target forms with the chains `D.Θ` |
| index, covolume | `TwistedLattice.IndexLe`, `TwistedLattice.CovolumeLe` | index at most ∑ δ_ℓ log ℓ: at each ι one integral matrix, the same for all twists of modulus prime to ℓ, with determinant of valuation at most δ_ℓ, makes the lifts of the family integral (`TwistedLattice.integralVectors`); covolume: a bound for the logarithm of the Gram determinant of the untwisted lifts at every conjugate |
| main amount, remainder | `D.mainAmount`, `D.totalRemainder` | m·k times the cost `D.directionAmount` of one direction; the prime sums at the a-places less their expected value |
| prime sum, gain | `D.primeSum`, `D.localPrimeSum`, `D.gain` | the sum of Λ(ν)(1 − χ_K(ν))·(y/ν − κ(−νσ))₊ over 1 ≤ ν ≤ a, at an order y and a place σ; its part at p divided by 2 log p, and the exponent of p asked to divide the composite lift |
| error unit, budget | `D.errorUnit`, `D.denominatorBudget`, `Selmer.clearingBound` | unit f·a·(log b)³ of the errors; that unit divided by m·k, which bounds the sum over ℓ of the numbers β_ℓ, where a determinant of ℓ-adic size at least exp(−dim·r·β_ℓ) clears the denominators of one lift (`D.ClearsProjection`); the share of one ℓ, as an exponent of ℓ |
| source form | `D.SourceForm`, `D.ramifiedSourceForms` | algebraic modular form on U(X₀), of weight (a, 0, …, 0) at the a-places and 0 elsewhere, of level principal at the chosen places with last row ≡ (0, …, 0, 1) mod π_N (`D.levelX`); ramified if its mean under the scalings at each prime dividing `D.piN` is 0 |
| target form | `D.targetForms` | good form on U(Y₀): parameter `D.targetParameter` at infinity, level principal at the chosen places only, so no level at N or at the twist (`D.principalForms`) |
| label | `IsLabel`, `labelIdem` | monic squarefree polynomial of degree r over a residue field, nonzero at 0, naming one of Green's characters of GL_r and its idempotent |
| good form | `D.goodForms`, `D.e₀` | image of the sum of the idempotents of good families of labels (`D.goodTupleFamilies`) in the forms of principal level. Good: no label has a root in its residue field that is a q₂-th root of unity, and above each of p₀, p₁ at least one label is primitive (`IsPrimitivePolynomial`: irreducible, with a root that generates the units of the extension of degree r) |
| setting of a lift | `Selmer.IsLiftSetting` | labels at the chosen places of a `DescentPair` to which the Selmer bounds of `New/Congruences` apply |
| cut | `Floors.PlaceData.IsCut` | truncated Bessel function |
| lift | `Space.lift`, `Kernel.lift`, `D.lowerChain`, `D.goodLift` | theta lift: adelic, by class sums, the chain Y₀ → Y_m, and W_j → V_j. The folder `New/Congruences/Lifting` is p-adic Hodge theory, and the predicate `Lift` is Shintani lifting |
| string | `Grading`, `Selmer.HasLiftTrace` | the m − 1 − j vectors added to X_j to give Y_j, j < m: hyperbolic pairs, and a middle vector if their number is odd. Also the sum of consecutive powers of the inverse cyclotomic character in the representation of a lift |
| jet | `jet`, `schurJet` | P(∂)F(0), a Taylor coefficient of a theta function |
| seesaw | `D.seesaw_identity` | on ramified source forms, `D.lowerChain` ∘ (Poincaré series) is c times `D.compositeLift` for a chain datum of the twist, with one c ≠ 0 for all twists; the right side is a finite combination of chains X₀ → X_m restricted to Y_m, and the theorem does not say that it is nonzero; an iterated seesaw identity |
| filling | `Filling`, `D.isSpread_goodPoincare` | translates of Poincaré series (`D.poincare`) spread over the target forms; a Petersson-type second moment |
| floor | `Shape.Form.floorGroup` | step of the tower of subgroups fixing the first hyperbolic pairs |
| exchange | `Exchange.exchange_identity` | for matched ramified data, a given real vector for V′ and a real vector for V that is only shown to exist (it is fixed before the modulus and the character), theta integrals over U(V), U(V′) of complementary rank agree up to a number c ≠ 0 that depends on the modulus and the character, where ‖c‖² is a fixed number times residue cardinalities and squared partial L-values; of Siegel–Weil type |
| square | `Exchange.one_square_identity_of_isEdgeFamily` | lift and transposed lift commute around a square after summing over matched data modulo the modulus, up to a factor κ/c, with c depending on the character and the modulus: κ does not depend on the character, the modulus or the forms, is not computed and is not shown nonzero here; ‖c‖² is a fixed number times residue cardinalities and squared partial L-values |
| grid, path, turn | `D.gridSpace`, `TwoGridPath`, `TwoGridPath.Turn` | spaces joined by lifts and transposed lifts; a monotone path through two grids; the move of a path across one square. The first path becomes the last by m² turns (`D.exists_transfersPeriods_first_last`) |
| auxiliary form | `D.IsAuxiliaryForm` | target form that completes a family to a basis in the lower bound |
| descent pair | `DescentPair` | the data of one lift W → V, with V definite, and of its descent |
| false lift | `DescentPair.falseLiftsAt` | form on V_j in the image of `D.e₀` that is orthogonal to the lifts and, like them, is killed by a Hecke polynomial operator at a split place off the level |
| type | `typeKernel`, `Space.IsForm` | kernel at infinity that reproduces a form (its discrete series). Also local types (`HasParahoricType`) |
| gauge | `weylGauge`, `GaugeLe` | p-adic norm of the values of a form; integral means gauge ≤ 1. Unrelated: `Floors.Gauge`, `Filling.maxGauge` |
| denominator, regular | `Selmer.DenominatorLe`, `D.IsRegularFamily` | ℓ-adic size of the projections to the lifts of integral forms orthogonal to the false lifts (a congruence number); twists of modulus prime to ℓ whose j-th power makes it small for W_j → V_j and for the lifts from U(1) of the main pairs for j (`D.HasDenominatorsLe`), and whose first m powers and their inverses have, for ramified pairs, inverse ratios of L-values of height at most x₁ (`D.HasSmallRatios`) |
| size | `D.jetSize`, `LevelPlaces.LevelForm.normSqAt` | logarithm of a squared norm, bounded at every conjugate σ; s_∞(j) = log j! + j log(M/Ω) is what a derivative of order j is charged |
| pair, ramified pair, main pair | `D.CriticalPair`, `Data.CriticalPair.ratio` | a point 1 ≤ z ≤ t and a character ν of U(1) of weight −c, z ≤ c ≤ 4b; its ratio is ‖L(z, (νϑ)⁻¹)‖ / ‖L(z, ν⁻¹)‖ without the factors at the level; ramified: exactly at the chosen places; main for j: m < z ≤ r, tame part that of lift j, weight near κ_j |
| normalisation | `D.invGainFactor`, `D.normalizedPoincare` | c_B = ∏ ℓ^(−g_ℓ) with g_ℓ = ⌊gain − error⌋ (`D.gainExponent`); 𝔭 = c_B c_ss⁻¹ #Ḡ·e₀𝒫 with Ḡ = `D.chosenGL` and 𝒫 = `D.poincare` |
| determinant | `D.chainDeterminant`, `D.liftDeterminant` | det(u*u), for the chain u on the target forms, or for the lift W_j → V_j on the good forms; `D.liftDeterminant ϑ j` takes the twist ϑ^j |
| composite lift, chain datum | `D.compositeLift`, `D.IsChainDatum`, `D.restrictedChain` | finite combination of chains of m lifts between the definite spaces X₀, …, X_m, glued in pairs of lifts (`D.gluedTensor`), then restricted to Y_m and multiplied by a product of powers of the conjugates of π̄_N (`D.restrictToY`); its coefficients, integral away from the modulus of the twist and bounded in size only for the empty modulus; its expansion in translates of the vacuum (`New/Derivatives/Vacuum`), used for sizes and at primes p ≠ N (`D.IsChainDatum.exists_isWeakChainDatum_compositeLift_eq`) |
| idle direction | `D.directionAmount` | one of the about k further directions in which a lift differentiates; each is charged the upper bound for its size less its guaranteed divisibility, and `D.heightLe_liftDeterminant_ratio` repays it |
| exceptional, marked | `D.IsExceptional`, `D.IsMarked`, `D.IsFullMark` | an inert prime p ≢ ±1 mod m for which the place −p^e is an a-place for some odd e with p^(e−1) < m; a set of primes above p, induced by a-places, with at most one of each conjugate pair for an exceptional p below x₁; full if it meets the pair induced by every a-place |
| stably unramified | `HasPrimitiveRoot5040` | CM field that contains a primitive root of unity of order 5040; then E/E⁺ is unramified at the finite places |
| polar | `IsPolar` | function E = O(e^v) whose transform ∫₀^∞ E(v) e^((1−s)v) dv is meromorphic, with at most simple poles, of given residues, in re s > 0 |
| rapid | `Space.IsRapid` | decaying faster than every power of `Space.height`, which measures the distance into the cusp |
| edge, arrow | `IsEdge`, `IsArrow` | edge: real theta datum that lifts forms of one type to another, in both directions; arrow: adelic datum that does so in one direction, from rapid forms |
| carrier | `Rows.carrierForm` | one theta lift of the constant function 1, the same for all twists |
| tie | `Selmer.tieRelations` | linear relation between the values of a cocycle at a tame generator and at a Frobenius element of an auxiliary place |
| even class, odd class | `Selmer.evenClasses`, `Selmer.shaOdd` | cocycle modulo ℓ^ν in a Tate twist, with local conditions above ℓ, unramified off ℓ (even classes: and off the added places), even or odd under complex conjugation; for the twist 0 odd classes have no parity condition |
| most Frobenii | `mostFrobenii` | filter on Frobenius data; a property that holds for most of them holds on a dense set |

Letters used in comments, and their names in Lean:

| Letter | Lean |
|---|---|
| q₀, q₁, q₂ | `P.q₀`, `D.q₁`, `P.q₂` |
| Φ_a, Φ_b | `D.aPlaces`, `D.bPlaces` |
| κ(τ), κ_j, κ̄ | `D.weight`, `D.liftWeight`, the geometric mean of the κ(τ) |
| p₀, p₁, M | `D.levelPrime`, `D.M` |
| π_M, π_N | `D.piM`, `D.piN`; π_N is an integer of E with π_N π̄_N = N |
| Δ, Δ/2 | `D.gap`, `D.halfGap` |
| Ω, rd_E | `P.bigOmega`, `D.rootDisc` (root discriminant of E); in Galois theory Ω is also the algebraic closure of ℚ |
| R_q, c_q | `primeRemainder` (∑ Λ(n)(1 − χ_K(n))(1/n − 1/x) over n ≤ x, n ≡ 1 mod q, less log x/φ(q) and less c_q), the real part of `logDerivMean d q 1`; c₁ is the case q = 1 |
| s_∞, s_fin, s_main | `D.jetSize`, `D.primeSum`, `D.mainPrimeSum` |
| h_dir, h_main, rem | `D.directionAmount`, `D.mainAmount`, `D.totalRemainder` |
| ξ, ξ_ι | a twist, ϑ in the code; the member θ ι of a family |
| Θ_ξ, s𝔭 | `D.lowerChain` (on the target forms `D.Θ`), `D.normalizedPoincare s` |
| c_B, c_ss | `D.invGainFactor`, `D.seesawConst` |
| Z(ξ), Z_j | `D.chainDeterminant`, `D.liftDeterminant` |

Some comments, names and file names use other words: column for source form (also a column of a diagram), row for target form (in `New/Congruences` also an ℓ-adic representation that satisfies `Selmer.IsMainSummandLike`), volume for determinant, thick for b-place (or b-letter), fit for regular, and auxiliary pair for descent pair.

## 3. Sizes

q₀ and d are fixed, and x → ∞; x is the point at which R_{q₀} is bounded above. The numbers q₁ = q₀T, q₂ = (q₀d)^(s+6) and Ω = exp(γ − Re L′/L(1, χ_K))·2π/rd_E depend on x, although `P.q₂` and `P.bigOmega` carry the prefix P. The primes p₀, p₁, N are ≡ 1 mod q₂², and κ_j(τ) = κ(τ) + (j + 1/2)Δ. The scales x, x₁ and b are integers, stored with their logarithms (`D.logX`, `D.logX₁`, `D.logB`). The lemma `D.scale_inequalities` collects five bounds: (log b)¹⁰⁰ ≤ x, x^(10⁶) ≤ x₁, x₁^(10⁶) ≤ b, (log x₁)⁶ ≤ log b and log log b ≥ 10¹²·`P.constantBound`. Here `P.constantBound` bounds the constants that depend on q₀ and d only. With the table below, log b, x, x₁, b, M, N increase in this order. For 0 < ε < 1/100, `eventually_exists_data` takes x₁ = ⌊exp(x^(ε/6))⌋ and log b in [x^ε, x^ε + 1].

| Letter | Role | Size |
|---|---|---|
| m | number of lifts, a power of 2 | in [√x, 2√x] |
| r, k | ranks, r a power of 3, k = r + 1 − m | r in [x⁵, 3x⁵], k in [r/2, r] |
| t | the ranks n_j = k + j(t + 1) grow by t + 1 | 5r |
| s = `D.towerExp` | exponent of 2 in q₁/q₀, 2^s = m²² | at most 32 log x |
| l₀ = `l₀ s` | least power of 3 above 27s | at most 81s |
| T = `towerDeg s` | number of a-places, 3·l₀·2^s = q₁/q₀ | in [x¹¹, x¹¹ (log b)^(1/5)] |
| f | number of infinite places of E | T φ(q₀) |
| Δ | the gap between the weights of consecutive lifts | 2r⁸ |
| a | the order of the derivative at the a-places | x·b |
| M | product of the primes p₀, p₁ | in [b²⁰, b²²] |
| N | level, a prime | log N within √(log b) above log N₋, N₋ = κ̄^m (M rd_E/2π)^(m−1) b^(−15/2) (`P.logLevelMin`); so in [m log b, 30 m log b] |
| `D.errorUnit` | unit of the errors | f a log³ b |

There are at least T / log b b-places. Y₀ is X₀ plus ϱ = `D.ϱ` hyperbolic planes and one line of norm −N (`D.spaceY_gram_eq`), with m = 2ϱ + 2.

Constants. 18480 = 16·3·5·7·11 divides q₀. The parameters ask q₀ ∣ 2(d + 1) and q₀ ∤ d + 1 (`New/Reduction/Data/FieldsAndPlaces`), so 16 ∣ 2(d + 1) and d ≡ 7 mod 8. Primes dividing q₀ split in K, so a prime that does not split is at least 13 (`Parameters.thirteen_le_of_chiK_ne_one`). 5040 = 7!, the order of the root of unity in `HasPrimitiveRoot5040`, divides q₁. For 0 < ε < 1/100 and large integers x, R_{q₀}(x) ≤ (64 φ(q₀) + 3)·x^(−1/2 + 6ε); the exponent comes from log⁶ b / m with log b ≤ 2x^ε (`eventually_primeRemainder_natCast_le`).

The class `D.HasLogBound u F l` of `New/Reduction/Data/Magnitudes` states |F| ≤ exp l if `u` is true, and exp l ≤ F if `u` is false (`D.HasLogUpper`, `D.HasLogLower`). The exponent `l` is an output parameter: instance search computes it from the shape of F. Products add exponents. Sums take the maximum, plus 1 for an upper bound. `D.le_of_hasLogBound : F ≤ G` finds an upper exponent of F and a lower exponent of G. Its default argument compares them by `grind` with `D.scale_inequalities`. This is a linear problem in log x, log x₁, log b, log log b, log log x₁ and `P.constantBound`. `D.nat_le_of_hasLogBound` is the version for ℕ, and `Data.HasLogBound.pos` gives positivity.

## 4. Conventions

- `Lib` holds results classed as known in the literature and missing from Mathlib, with the steps of their proofs. It imports nothing from `New`. `New` holds the set-up, the steps of the argument, and known results stated on the data. This sorting is a working classification. The section "Relation to the literature" in a file's head gives sources or related work, and `INDEX.md` collects them. `REFERENCES.md` lists the citations and says which were compared with their sources.
- Both folders use the namespace `New`. The exceptions are `Statements.lean`, `Main.lean`, and some lemmas and definitions in Mathlib's namespaces. The names of the folder and of the namespace make no claim of novelty. Sub-namespaces need not follow folders.
- Local `seal`, `attribute` and `set_option` lines steer elaboration and automation. The options set inside files concern the transparency used in unification, the size of instance search, and one warning. Local instances can matter for reading a statement.
- Many objects come from `choose` or `epsilon` (`D.spaceY`). The lemmas next to them give their properties. Harish-Chandra parameters mostly appear doubled, so they are integers (`D.targetParameter` is not doubled).
- Letters recur. Φ: the group `D.Φ` of infinite places, the CM type `PlaceEmbedding.Φ`, or a theta datum. ι: an isomorphism ℂ ≃ ℚ̄_ℓ, an index type or, in comments, the chain `D.lowerChain`. ϱ: `D.ϱ` or the Heisenberg operator. ψ: the additive character, a tame part, or a discrete series coefficient. θ: a family of twists, the theta functional, or an eigensystem; ϑ is one twist. G: the adelic group `G` or `Filling.G`. κ: column counts of a diagram, the weight `D.weight` in comments, or the index type of X₀. s: the exponent `D.towerExp`, a list of signs, an element of `D.chosenGL`, or the complex variable. d: `P.d` or, in comments, the dimension `D.targetDim`. D: the data or, in comments, a dimension. In comments also: μ_j⁰ for the character `D.untwistedLiftChar j` of lift j, ω for `D.chiMLocal`, w and w_j for κ and κ_j, π for π_N, and N for `D.chosenGroupOrder` in the Selmer bounds.

## 5. Global settings

`Lib/Speed`, imported through `Lib/Base`, holds the main settings that apply to the whole development. They steer instance search and `simp`. They add no axiom. With `Lib/Speed` emptied, every file still compiled on Lean v4.33.1. They can influence which instance a statement inside the development picks up, but not the five theorems: their types are constants of Mathlib and of `Statements.lean`, which does not import the settings. Apart from these, `lakefile.toml` sets options for all files: no automatic implicit variables, `maxHeartbeats`, `maxSynthPendingDepth`, the thread stack and one printing option.

| Setting | Effect on what you read |
|---|---|
| Changed `simp` set | `attribute [simp ←, simp]` tags a list of Mathlib lemmas in both directions, which erases them from the default set of every importing file. A proof names such a lemma when it needs it. |
| `IsVoid` | `simp` rewrites `IsEmpty α` to this synonym and stops there. |
| Instance priorities | A list of Mathlib instances is tried later. A second, short list is in `Lib/General/NumberTheory/CoefficientRings`, and some instances of the development have low priority. |

Besides these, five Mathlib lemmas get the tag `fun_prop` where they are first needed, and some definitions of the development are marked irreducible. Other settings end with their declaration, section or file: `seal … in`, `open scoped Classical in`, `set_option`, a few `attribute [-simp]`, `attribute [-instance]` and `attribute [local simp]` lines, and `attribute [local instance low] Fintype.ofFinite` in files that sum over finite types. A name in an `open` line may switch on scoped instances, coercions or `simp` lemmas of the development.

Coercions hide routine maps. A bundled object is read as its type (`DiscreteModule`, `Lift.GalLattice`). A form, a representation, a functor or a valuation subring is applied like a function: `F g`, `ρ g`, `F A`, and `A x` for the valuation of `x`. An element of `U J` is read as a matrix, an element of `E` as an adele, a point of `Gf` (the finite adelic points) as a point of `G`, a polynomial as a vector of Fock space, and a twist as its tame character.

Some data are classes, so statements do not name them. `ThePrime p` fixes a prime p. `PadicIso ℓ` fixes ℂ ≃ ℚ̄_ℓ, and `PadicPlace p` fixes ℂ → ℂ_p. `CMType E` fixes the embeddings Φ. `WeilData E` fixes the data of the Weil representation. A statement speaks of the instance in scope.

A hypothesis of the form `(h : … := by tac)` is proved by `tac` when the caller omits it.
