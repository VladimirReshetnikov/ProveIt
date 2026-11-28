# Contents

`New` is listed in the order of the argument, `Lib` by subject. Inside a folder, a file comes after the files it imports. The number is the count of code lines.

The heads of these files give an overview of a theory: `Lib/ClassField/Global/ArtinReciprocity`, `Lib/PadicHodge/Limit/TraceLimit`, `Lib/Cyclotomic/OddSha`, `Lib/PadicHodge/Kisin/FrameTheorem`, `Lib/Cohomology/WoodsHole`, `Lib/PadicComparison/CrystallineFrobenius`, `Lib/Shimura/Eigenspace`, `Lib/GaloisRep/Main/AllRanks`.

## New

### The theorem and its reduction

**From a one-sided bound to the zeros**

- `New/Reduction/Zeros/PrimeError` (293): A weighted prime-counting error term and its poles at zeros of L-functions
- `New/Reduction/Zeros/Criterion` (53): The one-sided criterion for a zero-free half-plane
- `New/Reduction/Zeros/PrimeNumberTheorem` (151): The prime number theorem for the remainders `R_q`

**Lattices, colength and heights**

- `New/Reduction/Lattices/Colength` (147): Colength of modules, and endomorphisms surjective up to a bounded colength
- `New/Reduction/Lattices/Heights` (128): The height of a family over all places: products, monotonicity and the product formula
- `New/Reduction/Lattices/TwistedLattice` (291): Twisted lattices

**The data**

- `New/Reduction/Data/FieldsAndPlaces` (267): The parameters q₀ and d, the field E = K(ζ), its infinite places and its roots of unity
- `New/Reduction/Data/AdmissibleData` (162): Admissible data
- `New/Reduction/Data/Magnitudes` (332): Logarithmic bounds for the sizes of the data
- `New/Reduction/Data/Existence` (640): Admissible data exist at every large x
- `New/Reduction/Data/LevelAndTwists` (177): Weight bounds, the level N, and twists and m-fold twists for chains of lifts
- `New/Reduction/Data/Sizes` (113): Sizes of the data

**Three theorems and the main inequality**

- `New/Reduction/PrimeSums` (185): Prime sums: main amount, expected value and total remainder
- `New/Reduction/IntegralTargetForms` (51): The target forms as a twisted lattice
- `New/Reduction/ShortAndEnough` (273): Theorem A (short forms) and Theorem B (enough forms)
- `New/Reduction/MainInequality` (65): The main inequality
- `New/Reduction/OneSidedBound` (199): The one-sided bound, and the theorem in half-plane form

### Derivatives of theta functions

**Derivatives that count primes**

- `New/Derivatives/Divisibility/NullFrames` (297): The change of directions
- `New/Derivatives/Divisibility/NormalForm` (280): Couplings and the normal form
- `New/Derivatives/Divisibility/Count` (522): Divisibility of the jets of a series with the normal form along products of minors

**The field and its characters**

- `New/Derivatives/Field/PrimeDecomposition` (533): Different and prime decomposition of the CM field E = K(ζ)
- `New/Derivatives/Field/WeilData` (332): Weil data of the CM field E = K(ζ) and the number s₀
- `New/Derivatives/Field/ChosenPlaces` (236): Chosen places, characters of given weight, finiteness of pairs and sizes of the different

**The formal group and the exponential factor**

- `New/Derivatives/FormalGroup/FrobeniusCongruence` (294): Frobenius congruence for `θ` and the coefficient of `z ^ (p - 1)` in `x`
- `New/Derivatives/FormalGroup/Exponent` (517): The exponent on one curve
- `New/Derivatives/FormalGroup/Resolution` (127): Resolutions of the identity and power series in the compositions `y(μ_i z)`
- `New/Derivatives/FormalGroup/ThetaProducts` (300): The normal form of theta products at non-split primes

**The integral vacuum**

- `New/Derivatives/Vacuum/TightFrames` (558): Scale of theta Taylor series, tight frames, jet series along lines
- `New/Derivatives/Vacuum/IntegralVacuum` (357): The integral vacuum θ°: integrality and bounds of its values, standard data at p
- `New/Derivatives/Vacuum/JetIntegrality` (191): Integrality of jets of theta products and stability of standard data
- `New/Derivatives/Vacuum/Scale` (77): The scale of the Taylor series of a vector
- `New/Derivatives/Vacuum/ShortVectors` (538): Tight frames in `𝔞₀`
- `New/Derivatives/Vacuum/StandardDataProducts` (355): Standard data as products of theta functions of the curve
- `New/Derivatives/Vacuum/Divisibility` (133): Integrality and divisibility of the derivatives of standard data

**The bound is attained**

- `New/Derivatives/Sharpness/OneCurve` (231): Derivatives of integral expansions
- `New/Derivatives/Sharpness/LeastValuation` (386): Least valuations of coefficients of theta products
- `New/Derivatives/Sharpness/Couplings` (404): Least valuations along couplings
- `New/Derivatives/Sharpness/NearPairs` (275): Near pairs of `b`-places and the losses in the sharpness bound
- `New/Derivatives/Sharpness/Cases` (443): The valuation bound `v(l!) + val₁₂(l) ≤ S_p + 2 ∑ v(B_τ)` for every prime
- `New/Derivatives/Sharpness/BoundAttained` (283): Sharpness of the valuation bound

### Upper bound: a composite lift

**Theta kernels between definite spaces**

- `New/UpperBound/Kernels/JetConjugatesAndBounds` (550): Galois conjugates of jets of theta functions and archimedean bounds for jets
- `New/UpperBound/Kernels/ThetaLiftGauge` (326): p-adic gauge bounds for one theta lift and data from functions modulo an ideal
- `New/UpperBound/Kernels/DefiniteKernelSize` (222): Rational equivariance, integrality and size of definite theta kernels

**Source forms, target forms and chains of lifts**

- `New/UpperBound/Objects/InsertBlock` (194): Inserting a block into a parameter
- `New/UpperBound/Objects/LiftLawsModuloN` (570): Direct and mirror data modulo `N`, and the operator `Up`
- `New/UpperBound/Objects/AuxiliaryPair` (633): Descent pairs: descent data for theta lifts to definite unitary groups
- `New/UpperBound/Objects/LabelsAndIndexTypes` (202): Good labels, index types of hermitian spaces, the group 𝖦 and idempotent e₀
- `New/UpperBound/Objects/Weights` (384): Harish-Chandra parameters, weights and lift diagrams of the definite spaces
- `New/UpperBound/Objects/LiftChains` (361): Chains of theta lifts, jointly invariant combinations, and free levels
- `New/UpperBound/Objects/Parameters` (669): Index sets, signs and parameters of the grids; the parameters of every step correspond
- `New/UpperBound/Objects/Columns` (566): Levels of the chain, chain data, and the composite lift
- `New/UpperBound/Objects/Rows` (541): Spaces Y_j and W_j, the forms on them, and the target parameter
- `New/UpperBound/Objects/RowChain` (290): The chain of theta lifts ι_μ along the spaces Y_j: level, character and 𝖦-equivariance
- `New/UpperBound/Objects/PoincareMap` (157): The Poincaré map
- `New/UpperBound/Objects/CharactersAtLevel` (102): Characters of the lifts of the chain above the level N

**The seesaw identity**

- `New/UpperBound/Seesaw/IntegralAsCosetSum` (280): Integrals over a quotient as finite sums over cosets with controlled multiplicity
- `New/UpperBound/Seesaw/AdmissibleCombinations` (529): Graded lattices, integrality away from q and admissible combinations of translates
- `New/UpperBound/Seesaw/StandardLines` (370): The standard lattice of a graded space, line by line
- `New/UpperBound/Seesaw/GluedLevel` (88): Congruence levels inside the stabilizer of a glued lattice
- `New/UpperBound/Seesaw/Sandwich` (163): Bounds for the lattices of points on graded spaces
- `New/UpperBound/Seesaw/EdgePairEvaluation` (743): Finite zero terms and the evaluation of pairs of edges in the tower of spaces `Y_k`
- `New/UpperBound/Seesaw/Frequency` (211): The shift at a nonzero constant term maps lattices into lattices
- `New/UpperBound/Seesaw/LevelIdeles` (76): Valuations of the chosen ideles, and lattices and levels at the chosen places
- `New/UpperBound/Seesaw/NeighbourLattice` (665): The neighbour lattice of a pair of edges
- `New/UpperBound/Seesaw/NeighbourVacuum` (227): The vacuum of the neighbour lattice
- `New/UpperBound/Seesaw/AdmissibleEvaluation` (479): Finite evaluation of edge pairs takes translates of the vacuum to admissible combinations
- `New/UpperBound/Seesaw/GoodDatum` (373): Evaluated data as admissible combinations of glued translates of the vacuum
- `New/UpperBound/Seesaw/UnfoldingStages` (781): Unfolding the chain of lifts: double lifts and the functions of the unfolding
- `New/UpperBound/Seesaw/Cut` (226): The outer variables: finitely many classes, with weights
- `New/UpperBound/Seesaw/SeesawIdentity` (413): The seesaw identity and the top of the chain

**Divisibility of the composite lift**

- `New/UpperBound/Divisibility/JetExponent` (369): A lower bound for the divisibility bound by the gain
- `New/UpperBound/Divisibility/MarkedPrimes` (294): Marked primes above `p`, full marks and the scaled Hecke operator
- `New/UpperBound/Divisibility/ChainValuation` (261): p-adic gauge bounds for chains of theta lifts and restrictions to `Y_m`
- `New/UpperBound/Divisibility/ValuationAtNonSplitPrimes` (702): Valuations of lifts at non-split primes
- `New/UpperBound/Divisibility/HeckeEdges` (575): Elementary divisor bound for the scaled Hecke operator via edges
- `New/UpperBound/Divisibility/MarkOperator` (296): Elementary divisors of one scaled Hecke operator on the integral source forms
- `New/UpperBound/Divisibility/SetupAtLevel` (205): The places `Σ_N` above N and the set-up at p = N
- `New/UpperBound/Divisibility/ChainDatumExpansion` (272): Two invariant sums of translates attached to a chain datum
- `New/UpperBound/Divisibility/ValuationAtLevel` (342): N-adic valuation of the lifts between the X_j at the level prime N
- `New/UpperBound/Divisibility/ColengthAtLevel` (193): The colength of source forms at p = N
- `New/UpperBound/Divisibility/LocalDivisibility` (312): The divisibility of the composite lift at each prime

**Size of the composite lift; short source forms**

- `New/UpperBound/Size/ShortColumns` (626): Prime-by-prime divisibility measures; short forms span the ramified source forms
- `New/UpperBound/Size/ClassCount` (127): Explicit bound for the number of classes in the genus
- `New/UpperBound/Size/Estimates` (244): Numerical inequalities between the parameters of the data
- `New/UpperBound/Size/ArchimedeanSize` (321): Archimedean size of the composite lift, and passage to target forms by the good projection

**Elementary divisors of a Hecke operator**

- `New/UpperBound/ElementaryDivisors/TwistingData` (238): Frobenius cycles, the twisted action of GL_k(W), depth and defect
- `New/UpperBound/ElementaryDivisors/RootLemma` (655): Gauss filtrations, Stepanov's count and the root lemma
- `New/UpperBound/ElementaryDivisors/InvariantAverage` (614): An average on polynomials in the entries of a matrix
- `New/UpperBound/ElementaryDivisors/Edges` (492): Edges, halfway lattices and duality
- `New/UpperBound/ElementaryDivisors/Depth` (502): Few forms have only deep translates
- `New/UpperBound/ElementaryDivisors/FrobeniusFactors` (516): The substitution by Frobenius powers of generic matrices; weight and defect
- `New/UpperBound/ElementaryDivisors/AveragingMap` (365): Averaging: removing the terms of large defect in all Levi translates at once
- `New/UpperBound/ElementaryDivisors/PieriCone` (379): The Pieri cone, the step map and the slab: interlacing and volume of the cone
- `New/UpperBound/ElementaryDivisors/DefectCount` (635): The dimension of the forms of bounded defect
- `New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem` (818): Elementary divisors of the edge Hecke operator

### Spanning: a second moment

**The second moment and the spanning theorem**

- `New/Spanning/SecondMoment/PositiveType` (139): Functions of positive type and singular minors
- `New/Spanning/SecondMoment/FewTranslates` (404): Few translates fill
- `New/Spanning/SecondMoment/SpanningTheorem` (202): The dimension of the target and one good translate of the Poincaré map

**Equality of multiplicities**

- `New/Spanning/Multiplicities/HeckeEigensystems` (283): Spherical Hecke operators away from the level, and eigensystems
- `New/Spanning/Multiplicities/EqualMultiplicities` (267): Equality of multiplicities

**Measures and Bessel functions**

- `New/Spanning/Bessel/Basic` (610): Bessel systems at a real place: length and norm bounds, lattice basis, discriminant
- `New/Spanning/Bessel/GramSection` (437): The Gram section γ_Z of the frame Gram matrix map on the unitary group G₁
- `New/Spanning/Bessel/Orthonormality` (142): Normalisation of a Bessel function and of its cut
- `New/Spanning/Bessel/MeanValue` (391): The mean value inequality over the Gram matrix of two frames
- `New/Spanning/Bessel/SobolevBound` (454): Unfolding bounds over G₁ and the L² bound at the section γ_Z via Sobolev
- `New/Spanning/Bessel/Average` (89): The group of the Bessel period at a real place
- `New/Spanning/Bessel/OpenCellBound` (459): Bounds near a point of Ω and the open cell bound for a Bessel system
- `New/Spanning/Bessel/OpenCellPairing` (170): One pairing on the open cell, at all places together
- `New/Spanning/Bessel/LargeFunction` (501): Bessel systems of discrete series type and a Bessel function large at a point
- `New/Spanning/Bessel/CutTailBound` (308): The Bessel function at a real place: decay and cut
- `New/Spanning/Bessel/SchurBound` (208): Schur's bound for a Bessel function and its derivatives
- `New/Spanning/Bessel/FillingData` (370): Filling data from admissible data, with Bessel systems at the real places

**Unfolding, and the proof of the moments**

- `New/Spanning/Unfolding/Setup` (336): The data, standing hypotheses and amplitudes of the filling theorem
- `New/Spanning/Unfolding/BesselLevelStructure` (560): Bessel data: level subgroup, Eichler maps and strong approximation for the unipotent group
- `New/Spanning/Unfolding/Terms` (360): Near terms in the filling theorem: frames, cell ranks, nearness and integrality
- `New/Spanning/Unfolding/Link` (571): Links of isometries, the link isometry Υ_γ, and invariance under `besselU`
- `New/Spanning/Unfolding/ReducedPoints` (475): Eichler-type unipotent elements, colouring bounds and reduced points
- `New/Spanning/Unfolding/Packing` (377): Class cutoffs and counting frames in boxes
- `New/Spanning/Unfolding/CutoffIntegral` (480): The Bessel kernel and the integral of a class cutoff over the real unipotent group
- `New/Spanning/Unfolding/AmplitudeSums` (631): Sums of amplitudes over blocks
- `New/Spanning/Unfolding/Climbing` (789): Residue lifts, lattice charts and common flag vectors: which filling terms contribute
- `New/Spanning/Unfolding/ReducedGroups` (421): The finite groups `Ū`, `H̄` and `R̄`
- `New/Spanning/Unfolding/TermStructure` (566): The structure of a term
- `New/Spanning/Unfolding/SquareExpansion` (474): The expansion of the squares and the second moment near the Bessel subgroup
- `New/Spanning/Unfolding/MomentBounds` (376): The second moment over the whole group
- `New/Spanning/Unfolding/Moments` (746): The second moments of the operators `P* s P`, and good forms
- `New/Spanning/Unfolding/PoincareSeries` (649): Poincaré series of fitting spaces, unfolding, Petersson products and source form coordinates
- `New/Spanning/Unfolding/BesselFormula` (249): The Bessel function as an integral over `R(F_∞)`
- `New/Spanning/Unfolding/FrameMass` (239): Masses of spheres and of frames
- `New/Spanning/Unfolding/FillingAdmissible` (529): Filling data for admissible data: fit to Y₀, Bessel bounds, standing hypotheses
- `New/Spanning/Unfolding/SeriesPeriod` (503): The Poincaré map as a Poincaré series of the Bessel function

**The remaining terms**

- `New/Spanning/RemainingTerms/SiegelLemma` (451): Discriminants of sublattices, Siegel's lemma and a height zeta function of subspaces
- `New/Spanning/RemainingTerms/Box` (218): The box
- `New/Spanning/RemainingTerms/BorderedDeterminant` (417): Links, lifts and gauges of a term
- `New/Spanning/RemainingTerms/FrameCount` (496): Frames of near terms: short shared vectors and moves between frames
- `New/Spanning/RemainingTerms/ColumnLattice` (186): The covolume of the lattice of columns
- `New/Spanning/RemainingTerms/OneRealPlace` (712): The weight of Schur's test at one real place
- `New/Spanning/RemainingTerms/SchurTest` (212): Schur's test: Cauchy–Schwarz and integration in stages
- `New/Spanning/RemainingTerms/Discriminants` (505): Discriminants of lattices and sums over sublattices
- `New/Spanning/RemainingTerms/OrbitSize` (272): Near terms in the filling theorem: the bound for an orbit, the tail and the open-cell term
- `New/Spanning/RemainingTerms/Data` (61): The data of a term and of a pair of terms
- `New/Spanning/RemainingTerms/OrthogonalLifts` (354): Orthogonal lifts and the two isotropic lists of a link
- `New/Spanning/RemainingTerms/LinkLattice` (626): The lattice of a link
- `New/Spanning/RemainingTerms/FrameParts` (464): The part in `X₀` of a frame, moves, and lifts of a lattice
- `New/Spanning/RemainingTerms/FramesOverLattice` (424): Counting frames over a lattice of small discriminant
- `New/Spanning/RemainingTerms/LatticesOfCorank` (582): Sums over lattices of given corank and small discriminant
- `New/Spanning/RemainingTerms/SchurOrbit` (741): Schur's test for one orbit
- `New/Spanning/RemainingTerms/Denominators` (131): Denominators: bases of `A⁺ / I_γ` and `γ A⁺ / I_γ`
- `New/Spanning/RemainingTerms/LinkVectors` (305): The vectors `z⁺` and `Υ_γ⁻¹ z⁺`
- `New/Spanning/RemainingTerms/Size` (541): The orbit bound: a bound for a block of amplitudes; the second moment of a set of terms
- `New/Spanning/RemainingTerms/Cut` (504): The cut: from the lattice of a link to the vectors common to two links
- `New/Spanning/RemainingTerms/Gain` (682): The gain: a discriminant bound for the common lattice of two terms over one block
- `New/Spanning/RemainingTerms/Count` (129): The sum over pairs of near terms
- `New/Spanning/RemainingTerms/Sum` (612): The remaining terms: a bound for their sum

**The main term**

- `New/Spanning/MainTerm/SieveSystem` (202): Sieve systems over places: products, positivity and lower semicontinuity
- `New/Spanning/MainTerm/KloostermanSum` (148): The orbital integral at the finite places is a Kloosterman sum
- `New/Spanning/MainTerm/Frequencies` (197): Sums over frequencies
- `New/Spanning/MainTerm/GlobalSieve` (811): One-sided Poisson summation, sums over frequencies, and the sieve over all places
- `New/Spanning/MainTerm/FillingLevel` (380): The place and level of a set of primes, orbit sums and the set of entries
- `New/Spanning/MainTerm/GlobalToLocal` (599): Class sums as orbit sums, and unfolding at a set of primes
- `New/Spanning/MainTerm/SiegelTopBound` (670): Siegel's formula as an upper bound, and domination of class sums by the density at the last entry
- `New/Spanning/MainTerm/FiniteSieveSystem` (202): The sieve system at the finite places
- `New/Spanning/MainTerm/EnergyEstimate` (475): Main-term bound for the second moment over open reductions fixing given vectors
- `New/Spanning/MainTerm/BadTypes` (197): The share of non-allowed polynomials and the bad share

**Two frames at one place**

- `New/Spanning/Frames/Lengths` (338): Sizes, lengths and balanced frames
- `New/Spanning/Frames/TwoGauges` (307): Comparing the lengths at two points; minors and heads
- `New/Spanning/Frames/Levels` (540): Place data, floor measures and depth
- `New/Spanning/Frames/Correlations` (340): The scale, near points and partial correlations
- `New/Spanning/Frames/QuadricVolumes` (392): Volumes on quadrics and on sections
- `New/Spanning/Frames/QuadricPlancherel` (295): Plancherel's formula on quadrics
- `New/Spanning/Frames/Depth` (644): Depth
- `New/Spanning/Frames/Densities` (481): The densities as integrals over pairs of frames
- `New/Spanning/Frames/OneFrame` (552): One frame
- `New/Spanning/Frames/Gains` (777): Two frames: separation and the gains at one position
- `New/Spanning/Frames/Shells` (192): The sum over the shells
- `New/Spanning/Frames/RealPlaceGauge` (989): Floor measures at the complex place: Haar measure, place datum and gauge
- `New/Spanning/Frames/RealShells` (523): Cut Bessel functions at ℂ: integration of the local estimates over shells
- `New/Spanning/Frames/RealBandLimits` (540): The normalized cell integral Ξ and the local bounds at ℂ for cut Bessel functions
- `New/Spanning/Frames/StandardLevel` (717): Place data and gauges at a finite place from the lattice of integral vectors
- `New/Spanning/Frames/BesselVector` (463): The Bessel vector at the finite places
- `New/Spanning/Frames/FiniteDepth` (394): Depth, heads and far positions at the finite places
- `New/Spanning/Frames/FiniteShells` (529): Shells, decay and mass at the finite places
- `New/Spanning/Frames/FiberMeasures` (366): Fiber measures of the standard form, and the top quadric by its last entry
- `New/Spanning/Frames/TopCorrelation` (550): Scaled orbital integrals of the finite Bessel vector on the floor group
- `New/Spanning/Frames/TopFloor` (536): The density at the last entry
- `New/Spanning/Frames/FixedLines` (632): Groups that fix given vectors at chosen places have a small mass integral

### Lower bound: the determinant

**A twist for each prime**

- `New/Determinant/Twist/FitTwists` (76): The ratio of twisted to untwisted Hecke L-values, main pairs and regular families of twists
- `New/Determinant/Twist/LongForms` (151): Theorem C: integral forms are long

**Norms of theta lifts**

- `New/Determinant/Norms/VectorKernel` (79): The theta kernel of a descent pair with values in the weight representation
- `New/Determinant/Norms/AdjointThetaLift` (662): The lift Θ_W, its adjoint and its norm

**The exchange identity**

- `New/Determinant/Exchange/NegativeIndices` (357): Theta coefficients vanish off negative forms
- `New/Determinant/Exchange/MatchingPartners` (413): Matched functions, sections over GL cosets and same-section pairs of matrix functions
- `New/Determinant/Exchange/EquivariantDifference` (223): The difference in the exchange identity as an equivariant lift
- `New/Determinant/Exchange/StableSpacesStandardData` (563): Criteria for a function with a matched function to lie in a stable space; vanishing of lifts
- `New/Determinant/Exchange/ConeImage` (319): The image of the cone integral
- `New/Determinant/Exchange/LargeTriple` (763): Parabolic theta terms, equal ranks, and the exchange identity for the large triple
- `New/Determinant/Exchange/RealVectors` (539): Smooth local Witt theorem and the exchange identity for `V' ⊕ W₁` and `V'`
- `New/Determinant/Exchange/RemovingPlanes` (434): Change of point and sign, and descent of the exchange identity by removing hyperbolic planes
- `New/Determinant/Exchange/VanishingDescends` (105): Vanishing of theta integrals descends along hyperbolic planes
- `New/Determinant/Exchange/TheoremForPartners` (720): Exchange of theta integrals for matched functions and for data modulo an ideal
- `New/Determinant/Exchange/OneSquare` (679): One square: up then down against down then up
- `New/Determinant/Exchange/ExplicitMatching` (603): Explicit real data: the exchange identity for a definite space with determinant data

**The norm of a chain of lifts**

- `New/Determinant/Chain/SquareLaw` (310): The finite square law for theta lifts: special data, matched functions and Fourier form
- `New/Determinant/Chain/TriangleNorms` (301): Orders of block triangular groups and Gram forms of chains in triangles
- `New/Determinant/Chain/Moduli` (266): Ratios of Hecke values and heights of functions of the twist
- `New/Determinant/Chain/TriangleLifts` (387): Theta lifts as a triangle of arrows: spaces, lifts, descents and the first lift
- `New/Determinant/Chain/ChainNorms` (523): Norms along the chain of theta lifts and injectivity of ι_ϑ
- `New/Determinant/Chain/NormOfChain` (292): The volume of ι on the target forms as a product of volumes of theta lifts

**Auxiliary forms**

- `New/Determinant/AuxiliaryForms/GridPaths` (218): Monotone paths through two square grids, and their turns
- `New/Determinant/AuxiliaryForms/RegularParameters` (98): Weights of regular parameters and bounds on boxes
- `New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod` (537): Steep parameters of Y₀ and Ỹ^0_0; periods of Poincaré series of deep level
- `New/Determinant/AuxiliaryForms/PathData` (454): Moduli, spaces, moves, path data and periods on the two grids
- `New/Determinant/AuxiliaryForms/DeepLevelVanishing` (529): Vanishing of forms on Y₀ orthogonal to the deep level on Ỹ^0_0
- `New/Determinant/AuxiliaryForms/GridFirstColumns` (520): Periods on the diagonal and path data on the first path
- `New/Determinant/AuxiliaryForms/Turns` (643): Turning path data, and turns off the diagonal
- `New/Determinant/AuxiliaryForms/DiagonalTurns` (459): Turns on the diagonal, and the transfer of periods from the first path to the last
- `New/Determinant/AuxiliaryForms/FirstPath` (262): The maps `Θ^♭` and `res^♭`, and the first path
- `New/Determinant/AuxiliaryForms/LastPath` (743): The branching pairing and the periods on the last path
- `New/Determinant/AuxiliaryForms/SpanningForms` (531): Denominators and sizes on the last path, and the auxiliary forms

### Lower bound: one lift

**One lift and Hecke values**

- `New/OneLift/TestedForms` (350): Point forms, Hecke adjoints and false lifts on the definite space of a descent pair
- `New/OneLift/LiftVolumeHeight` (528): The cost of one lift: a height bound for Z_j(1)/Z_j(ξ^j)

**The comparison operator**

- `New/OneLift/ComparisonOperator/OneExchange` (352): One exchange, and class sums at the level of a row stabilizer
- `New/OneLift/ComparisonOperator/GluedLattices` (514): Gluing: residue rings, divided lattices, the congruence group and glued lattices
- `New/OneLift/ComparisonOperator/GluedForms` (370): Gluing: the descent of product forms and the denominators
- `New/OneLift/ComparisonOperator/ExchangeData` (388): Data of the three exchanges: the carrier, the choices and the functions 𝖥_i
- `New/OneLift/ComparisonOperator/DeterminantProducts` (97): Products of determinants and first-column coordinates under substitution
- `New/OneLift/ComparisonOperator/ThetaKernelEstimates` (681): Decay of Fock matrix coefficients, sparse theta sums and the isolation estimate
- `New/OneLift/ComparisonOperator/LineCoordinates` (469): The polynomial map ζ, the datum Ψ^add and the series Υ; norm, degree and denominator of ζ
- `New/OneLift/ComparisonOperator/FirstFactors` (509): The first factors: P_V along W_j and W^add, integrality and size
- `New/OneLift/ComparisonOperator/ThreeExchanges` (562): Three exchanges: the carrier, the third exchange and its left side as a theta series
- `New/OneLift/ComparisonOperator/ProductsSpan` (595): Products span
- `New/OneLift/ComparisonOperator/GluingMaps` (703): The first factors and the gluing maps

**Periods of false lifts**

- `New/OneLift/FalseLifts/BottomOfTower` (1002): The bottom of the tower: from the block datum to all data
- `New/OneLift/FalseLifts/HyperbolicPlaneStep` (323): Vanishing of theta descents from W to W plus hyperbolic planes
- `New/OneLift/FalseLifts/PeriodsOfFalseLifts` (508): The tower of descents and the periods of false lifts

**Hecke L-values as squared norms, and their valuations**

- `New/OneLift/HeckeValues/CharacterLift` (455): The lift of a character from U(1): kernel, descent and Galois conjugates
- `New/OneLift/HeckeValues/CharacterLiftNorm` (325): The lift of a character and its squared norm as a Hecke L-value
- `New/OneLift/HeckeValues/TwistedRatio` (229): The algebraic part as a Hecke L-value, and products of L-values of twists
- `New/OneLift/HeckeValues/AlgebraicPartIntegrality` (192): The lift of a character: denominators, and one group ring element for all twists
- `New/OneLift/HeckeValues/AlgebraicPartSize` (357): Archimedean bounds and heights of squared norms of rank-one theta lifts
- `New/OneLift/HeckeValues/CentralAction` (217): Central action on lifts from U(1) and a rank-one denominator bound
- `New/OneLift/HeckeValues/TwistedValueHeights` (783): Heights of ratios of twisted to untwisted Hecke values via rank-one theta lifts
- `New/OneLift/HeckeValues/PeriodAtOne` (172): The period of a determinant theta kernel (used in rank two for the L-value at z = 1)

### Lower bound: congruences

**Congruences and the choice of twists**

- `New/Congruences/FitTwistsExist` (333): All data have regular families of m-fold twists

**Congruences and Galois representations**

- `New/Congruences/GaloisRepresentations/SelmerHypotheses` (372): Bad places, ℓ-adic avatars and hypotheses on conjugate self-dual representations
- `New/Congruences/GaloisRepresentations/AttachedRepresentations` (440): Lift settings and conjugate self-duality of attached Galois representations
- `New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels` (490): Main summands and conjugate self-dual representations from type polynomials
- `New/Congruences/GaloisRepresentations/BaseLevelOfLabel` (415): Base data whose forms contain those with given labels in a lift setting
- `New/Congruences/GaloisRepresentations/RowsFromEigensystems` (358): Main summand conditions on Hodge–Tate jumps and existence of main summands for Hecke eigensystems

**Congruences to first order**

- `New/Congruences/FirstOrder/RibetMethod` (433): Amitsur's formula and Ribet's method for matrices over an algebra
- `New/Congruences/FirstOrder/FittingBlock` (526): Modules of functions, Fitting ideals and trace ideals for Ribet's method
- `New/Congruences/FirstOrder/RibetMatrices` (691): Tied rows and the matrices of Ribet's method to first order
- `New/Congruences/FirstOrder/RibetLemma` (476): Ribet's method to first order over a discrete valuation ring
- `New/Congruences/FirstOrder/OnePrime` (551): Norms, logarithms and first-order deformations of the norm
- `New/Congruences/FirstOrder/EvenClasses` (132): Even classes and auxiliary places for Selmer cocycles
- `New/Congruences/FirstOrder/KummerMaps` (579): Kummer maps
- `New/Congruences/FirstOrder/TateTwistCocycles` (187): Cocycles of Tate twists: the even part and the triangle cost
- `New/Congruences/FirstOrder/TiedTraces` (530): Tied traces and the dictionary at one auxiliary place
- `New/Congruences/FirstOrder/TrianglePrimes` (456): Taylor–Wiles places in a triangle for the even classes, with prescribed Frobenii
- `New/Congruences/FirstOrder/AuxiliaryPrimeTie` (500): The family of operators at the auxiliary places
- `New/Congruences/FirstOrder/HeckeStrings` (309): Chains of roots for weak lifts, and Hecke-stable subspaces of forms
- `New/Congruences/FirstOrder/TraceRelations` (688): Constants, trace relations, lattices and local defects for Ribet's method
- `New/Congruences/FirstOrder/RibetElement` (263): Ribet's element for conjugate self-dual representations
- `New/Congruences/FirstOrder/DenominatorBound` (945): The bound for denominators

**Anticyclotomic twists with small Selmer groups**

- `New/Congruences/Selmer/AuxiliaryPrimes` (307): Auxiliary primes, anticyclotomic characters, slopes and ties
- `New/Congruences/Selmer/SelmerData` (421): Selmer data, tied Selmer groups and classes as functions
- `New/Congruences/Selmer/Count` (382): The dual of a tied Selmer group and the count
- `New/Congruences/Selmer/Mirror` (497): Reciprocity at conjugate primes
- `New/Congruences/Selmer/OneSystem` (290): The universal twist and one system of equations for all twists
- `New/Congruences/Selmer/Descent` (428): The descent
- `New/Congruences/Selmer/Untied` (364): The failure to be tied
- `New/Congruences/Selmer/StickelbergerSystems` (162): Stickelberger systems
- `New/Congruences/Selmer/StickelbergerLine` (383): Stickelberger systems on a line
- `New/Congruences/Selmer/Line` (421): Restriction to a line
- `New/Congruences/Selmer/RootsOfUnity` (353): Roots of unity `ζ` with polynomials hardly more divisible at `ζ - 1` than at given points
- `New/Congruences/Selmer/GeneralTheorem` (279): Twisting, general form
- `New/Congruences/Selmer/MainSummands` (230): Main summands are Selmer data
- `New/Congruences/Selmer/ClassSums` (292): L-values of a pair as integral measures, and avatars of tame characters
- `New/Congruences/Selmer/LValueSystems` (249): The Stickelberger systems of the L-values
- `New/Congruences/Selmer/TwistingTheorem` (291): The twisting theorem

**The local loss**

- `New/Congruences/LocalLoss/Basic` (359): Local loss above ℓ: main summand weights, b-places, crystalline relations and crystalline colength
- `New/Congruences/LocalLoss/CrystallineCocycles` (391): Crystalline cocycles and the defect of a crystalline lattice at a place above ℓ
- `New/Congruences/LocalLoss/CrystallineDefect` (416): The defect of the dual of a summand at a place above ℓ
- `New/Congruences/LocalLoss/TateDualBound` (153): A bound for non-crystalline cocycles modulo `ℓ ^ m` by the Tate dual lattice
- `New/Congruences/LocalLoss/LocalLattices` (147): Tame classes from roots of unity and lattices read at a place above ℓ

**Lifting crystalline extension classes in large weight**

- `New/Congruences/Lifting/ExponentLattices` (725): Lattices with prescribed orders, depth steps and the depth lemma
- `New/Congruences/Lifting/HodgeExpansion` (496): Exponents of lattice elements in a Hodge basis and the length of one step on a line
- `New/Congruences/Lifting/CupProductBound` (830): Sides of a pairing, cokernel killers and the pairing lemma for cup products
- `New/Congruences/Lifting/SidePoints` (504): Jump windows, the gap condition and points of the sides of a Kummer chart
- `New/Congruences/Lifting/TameCharts` (427): Tame Kummer charts and the power of p that kills cokernels of Kisin modules
- `New/Congruences/Lifting/LongGap` (307): The long gap lemma for a side of a Kummer chart, by expansion in powers of E
- `New/Congruences/Lifting/SafeMoves` (506): Safe moves and the walk for pairings of sides of a Kummer chart
- `New/Congruences/Lifting/CutExponentBounds` (683): Exponent bounds by cuts for paired sides of a Kummer chart: sparse thick letters, two sizes
- `New/Congruences/Lifting/DeepPoints` (247): Deep points and scaled cup coboundaries for a gap below zero or nonpositive jumps
- `New/Congruences/Lifting/FewLowJumps` (706): Few low jumps: length lost to depth and a submodule cupping to zero
- `New/Congruences/Lifting/CupOrthogonalityBounds` (363): From sides to lattices: few low jumps, b-letters and tame types

### Supplement

**Discrete series with a large gap**

- `New/Appendix/DiscreteSeries/SteepParameters` (49): Steep parameters and the setting of Laplace's method
- `New/Appendix/DiscreteSeries/Localization` (497): Localizing products of discrete series coefficients near the compact subgroups
- `New/Appendix/DiscreteSeries/MinorSecondOrder` (410): One minor of a product of three exponentials, to second order
- `New/Appendix/DiscreteSeries/Positions` (306): Positions of a smaller unitary group, and the two traces
- `New/Appendix/DiscreteSeries/StationaryPosition` (501): The stationary position
- `New/Appendix/DiscreteSeries/OneMinor` (429): One minor near the identity
- `New/Appendix/DiscreteSeries/GaussianShape` (271): The Gaussian shape of the coefficient
- `New/Appendix/DiscreteSeries/Periods` (366): Lower bounds for periods by Laplace's method
- `New/Appendix/DiscreteSeries/PositionGroup` (499): The group of a position

### The last file

- `New/Main` (32): From non-vanishing in Re s > 1/2 to zeros on the critical line

## Lib

- `Lib/Speed` (56): Speed settings
- `Lib/Base` (7): The adjoint of a matrix for the Hermitian dot product

### Adelic: Adeles, unitary groups and automorphic forms

- `Lib/Adelic/Landherr` (387): Sums of two squares, Landherr's theorem and the Hasse principle for unitary cocycles

**Adeles**: Adeles of number fields, characters and approximation

- `Lib/Adelic/Adeles/Basic` (663): Finite adeles of number fields: topology, idempotents, functoriality and base change
- `Lib/Adelic/Adeles/AdditiveCharacter` (269): The additive character, Haar measures and the rational lattice in the adeles
- `Lib/Adelic/Adeles/StrongApproximation` (437): Standard character, self-duality, strong approximation and one-sided Poisson summation
- `Lib/Adelic/Adeles/IdeleModulus` (311): The module of an idele, Haar measure scaling and the norm map on finite adeles
- `Lib/Adelic/Adeles/LocalFactors` (254): Idelic generators of ideals, semilocal fields and tame local characters
- `Lib/Adelic/Adeles/SemilocalProducts` (254): Products of completions at finite sets of places and approximation of adeles by elements of E

**AutomorphicForms**: Automorphic, cuspidal and algebraic forms

- `Lib/Adelic/AutomorphicForms/Basic` (254): Automorphic forms on adelic unitary groups, the Petersson product and rapid decay
- `Lib/Adelic/AutomorphicForms/RealConvolution` (367): Convolution over real points, cusp kernels, the Petersson product and Poincaré series
- `Lib/Adelic/AutomorphicForms/UnipotentRadical` (302): The mean along a unipotent radical vanishes; reduction in the radical
- `Lib/Adelic/AutomorphicForms/Cuspidality` (613): Cuspidality bounds, unipotent reduction, rapid decay and finite dimension of forms
- `Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms` (278): Algebraic forms on definite unitary groups, their pairing and Harish-Chandra parameters
- `Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic` (248): Automorphic forms on standard definite spaces as algebraic forms
- `Lib/Adelic/AutomorphicForms/HeckeEigenforms` (278): Algebraic modular forms: delta forms, unitary translation and spanning by Hecke eigenforms
- `Lib/Adelic/AutomorphicForms/BlockPeriods` (126): Periods of algebraic forms over a block subgroup as class sums via branching
- `Lib/Adelic/AutomorphicForms/PAdicGauge` (507): The p-adic gauge of algebraic forms, class sums, and integral forms of a level

**Hecke**: Hecke operators and class sums

- `Lib/Adelic/Hecke/Basic` (241): Level spaces, Hecke operators, stabilisers and class sums
- `Lib/Adelic/Hecke/ClassSums` (482): Class sums as integrals over Γ\G, orbit unfolding and means over compact subgroups

**QuotientMeasure**: Measures on quotients and unfolding

- `Lib/Adelic/QuotientMeasure/Basic` (482): Quotient measures via cutoffs: unfolding, covolume, unimodularity, periodic means
- `Lib/Adelic/QuotientMeasure/IwasawaUnfolding` (462): Unfolding over orbits and integration in Iwasawa coordinates
- `Lib/Adelic/QuotientMeasure/MovingTheQuotient` (58): Moving a quotient from one variable to another
- `Lib/Adelic/QuotientMeasure/UnfoldingInStages` (255): Pushing forward quotient measures, unfolding in stages and vanishing criteria

**Reduction**: Reduction theory for adelic unitary groups

- `Lib/Adelic/Reduction/FirstMinimumShortBases` (583): Transference, first minima and short bases of lattices of hermitian spaces
- `Lib/Adelic/Reduction/MinkowskiTheorems` (484): Adelic Minkowski theorems and counts of rational points in boxes
- `Lib/Adelic/Reduction/FiniteVolume` (494): Adelic reduction theory, Mahler's criterion and finite volume of the arithmetic quotient
- `Lib/Adelic/Reduction/DefiniteClassSums` (221): Mahler's criterion for hermitian spaces and class sums for definite spaces

**TraceFormula**: Trace formula for unitary groups of hermitian spaces

- `Lib/Adelic/TraceFormula/LineDeterminant` (243): Traces on the range of an idempotent from traces of a raising operator
- `Lib/Adelic/TraceFormula/LevelAlgebra` (60): The elements of a group algebra that keep a level
- `Lib/Adelic/TraceFormula/LineCount` (209): Lines and hyperplanes over a field
- `Lib/Adelic/TraceFormula/TestFunction` (150): Test functions and the two local conditions of the comparison of traces
- `Lib/Adelic/TraceFormula/CuspidalType` (177): An irreducible label in a tuple gives a cuspidal test function
- `Lib/Adelic/TraceFormula/FibreIntegral` (375): Integration over the fibres of a conjugation map
- `Lib/Adelic/TraceFormula/IsotropicStabiliser` (149): The stabiliser of an isotropic subspace
- `Lib/Adelic/TraceFormula/LineStabiliser` (547): The stabiliser of a line at a finite place
- `Lib/Adelic/TraceFormula/OffPlace` (81): Test functions with a deeper level at an auxiliary place
- `Lib/Adelic/TraceFormula/Stretch` (61): Rational points that pair short lattice vectors non-trivially
- `Lib/Adelic/TraceFormula/CoprimeFactors` (568): Coprime factors
- `Lib/Adelic/TraceFormula/LevelCut` (243): Passage to the stabiliser of a line at an auxiliary place
- `Lib/Adelic/TraceFormula/ChangingSigns` (279): Types of frames with a similitude, and the permutation of orbits that changes signs
- `Lib/Adelic/TraceFormula/KernelBound` (242): The sum of a majorant over the rational points
- `Lib/Adelic/TraceFormula/Convergence` (322): Convergence of the geometric side
- `Lib/Adelic/TraceFormula/ReduciblePolynomials` (160): The geometric side, polynomial by polynomial
- `Lib/Adelic/TraceFormula/OrbitalUnfolding` (429): Kernels of levels as forms, and unfolding of orbital integrals
- `Lib/Adelic/TraceFormula/TraceComparison` (492): Comparison of traces of operators on forms for different spaces and signs
- `Lib/Adelic/TraceFormula/CuspidalComparison` (67): Comparison of traces for a cuspidal test function

**Unitary**: Adelic unitary groups and hermitian spaces

- `Lib/Adelic/Unitary/Defs` (291): Adelic unitary groups over a CM field: levels, hermitian spaces, lattices and mass
- `Lib/Adelic/Unitary/ComponentsAndBlockSums` (297): Components of unitary adelic points at places; sums and moves of hermitian spaces
- `Lib/Adelic/Unitary/CongruenceLevels` (295): Principal levels and levels defined by reductions in the finite adelic unitary group
- `Lib/Adelic/Unitary/GramMatrix` (71): The Gram matrix of a space is invertible and hermitian; group elements from isometries
- `Lib/Adelic/Unitary/WeakApproximation` (246): Closed matrix embedding of adelic unitary groups, discrete rational points, weak approximation
- `Lib/Adelic/Unitary/RationalPoints` (128): Rational points and vectors of spaces under sums, moves and block embeddings

**Witt**: Witt's theorem, Eichler maps and Iwasawa decomposition

- `Lib/Adelic/Witt/WittTheorem` (461): Witt's theorem over fields and over Ô; quasi-reflections, Eichler maps, frames
- `Lib/Adelic/Witt/SmoothWitt` (73): Smooth families of isometries that carry an isotropic vector to its neighbours
- `Lib/Adelic/Witt/IwasawaDecomposition` (439): Maximal compact subgroup, splittings of isotropic frames and the Iwasawa decomposition

### Analytic: Analytic number theory

- `Lib/Analytic/ZeroSymmetry` (47): Zeros of L(s, χ) and of L(1 − s, χ⁻¹)
- `Lib/Analytic/PolyaVinogradov` (146): Gauss sums of primitive characters and the Pólya–Vinogradov bound
- `Lib/Analytic/DirichletTheta` (373): Theta series of Dirichlet characters, Poisson summation, and `L(s, χ)` as a Mellin transform
- `Lib/Analytic/EntireLFunction` (123): Quadratic twists, polar functions and logarithmic derivatives of Dirichlet L-functions
- `Lib/Analytic/Landau` (179): Landau's lemma
- `Lib/Analytic/QuadraticTwist` (620): A prime `d` in a class whose quadratic twists have no zero in a box
- `Lib/Analytic/Primes` (333): Primes congruent to `1` modulo `M ^ k` with logarithm in a prescribed window

**PrimeNumberTheorem**: The prime number theorem in progressions

- `Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth` (293): Growth of Dirichlet L-functions near the line `re s = 1`
- `Lib/Analytic/PrimeNumberTheorem/Tauberian` (291): A Tauberian theorem with a power of the logarithm
- `Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion` (150): A zero-free region for Dirichlet L-functions

### CM: Complex multiplication

- `Lib/CM/KroneckerLimit` (283): Kronecker's first limit formula
- `Lib/CM/GoodReduction` (541): CM lattices as multiples of fractional ideals, and good reduction of CM curves
- `Lib/CM/ConjugateCurve` (488): Galois conjugates of CM curves: conjugate sections, isogenies and translates of θ
- `Lib/CM/FiniteLattices` (114): Finitely many CM lattices
- `Lib/CM/ChowlaSelberg` (510): Odd class number, ζ_K = ζ·L(s, χ), theta functions with CM and Chowla–Selberg

**FormalGroup**: The formal group of a CM curve

- `Lib/CM/FormalGroup/IntegralParameter` (429): Integral series rings 𝔬[[T]], congruence parts of power series, a functional equation
- `Lib/CM/FormalGroup/PrimeNotation` (240): Notation at a prime, and elements of prime-power norm at split primes
- `Lib/CM/FormalGroup/InseparableDegree` (258): The inseparable degree
- `Lib/CM/FormalGroup/FormalParameter` (201): The formal parameter

**Integrality**: Integrality of expansions of theta functions

- `Lib/CM/Integrality/Doubling` (218): Doubling formulas for θ and σ and the quartic forms of doubling
- `Lib/CM/Integrality/TorsionValues` (261): Integrality of values of sections at torsion points
- `Lib/CM/Integrality/IntegralSections` (342): The integrality principle in one variable
- `Lib/CM/Integrality/IsogenyIntegrality` (81): Isogenies and translates act integrally on expansions
- `Lib/CM/Integrality/LogTheta` (445): The logarithm of the theta function of a CM lattice and the integral group law

**Sigma**: Sigma, theta and Weierstrass functions of lattices

- `Lib/CM/Sigma/Basic` (596): Sigma and Weierstrass functions, lattice invariants and lattices with complex multiplication
- `Lib/CM/Sigma/ThetaSections` (559): Theta functions of a CM elliptic curve: Weierstrass equation and spanning monomials

### ClassField: Class field theory and Galois cohomology

- `Lib/ClassField/Grunwald` (599): Grunwald's theorem in prime degree and CM steps with prescribed local behaviour

**Avatar**: ℓ-adic avatars of algebraic Hecke characters

- `Lib/ClassField/Avatar/HeckeBaseChange` (263): Base change of U(1) and Hecke characters, their L-functions and parallel twists
- `Lib/ClassField/Avatar/LocalGlobalCompatibility` (136): Local-global compatibility for the ℓ-adic avatar of an algebraic Hecke character

**GaloisCohomology**: Continuous Galois cohomology

- `Lib/ClassField/GaloisCohomology/ContinuousCocycles` (340): Continuous cohomology of discrete modules: cocycles, H², cyclic classes, local Artin map
- `Lib/ClassField/GaloisCohomology/ShapiroCorestriction` (230): Shapiro's lemma, corestriction and reduction of H² statements to steps of prime index
- `Lib/ClassField/GaloisCohomology/TateIndexFormula` (311): Coker/ker indices and Tate's index formula for cyclic actions of prime order
- `Lib/ClassField/GaloisCohomology/KummerCyclicClasses` (437): Cup products, Hilbert 90, Kummer cocycles and cyclic symbols in Galois cohomology
- `Lib/ClassField/GaloisCohomology/TameSelmerCocycles` (170): Selmer groups unramified outside a set and cocycles of tamely ramified actions

**Global**: Global class field theory

- `Lib/ClassField/Global/ArtinMap` (181): The global Artin map: product of local symbols, continuity, splitting and norms
- `Lib/ClassField/Global/AlbertBrauerHasseNoether` (472): Real place symbols, the second inequality and Albert–Brauer–Hasse–Noether
- `Lib/ClassField/Global/ArtinReciprocity` (366): Artin's reciprocity law and the sign law. Its head has an overview of the theory.
- `Lib/ClassField/Global/NormTheorems` (143): Surjectivity of the Artin map, Hasse's norm theorem and norm groups of cyclic extensions
- `Lib/ClassField/Global/CMSplittingCharacters` (593): CM fields: complex conjugation, invariant ideles and splitting characters
- `Lib/ClassField/Global/Chebotarev` (64): Chebotarev: Frobenii at primes of degree one in every nonempty open set
- `Lib/ClassField/Global/ExistenceTheorem` (706): Kummer characters, power indices and the existence theorem for totally complex fields

**GreenbergWiles**: Greenberg–Wiles counting of Selmer groups

- `Lib/ClassField/GreenbergWiles/SelmerLevels` (403): Selmer cocycles, N-units, split places and the equivariant S-unit theorem
- `Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity` (670): Trivialised cocycles and power residue relations at split primes
- `Lib/ClassField/GreenbergWiles/CocycleCounts` (539): Counts of trivialised Galois cocycles for projective modules and central scalars
- `Lib/ClassField/GreenbergWiles/SelmerRelations` (343): Relations at split primes and their number (Greenberg–Wiles)
- `Lib/ClassField/GreenbergWiles/Relations` (414): Relations at split primes
- `Lib/ClassField/GreenbergWiles/RelationsModL` (319): Relations modulo ℓ

**HeckeCharacter**: Hecke characters and characters of U(1)

- `Lib/ClassField/HeckeCharacter/Basic` (513): Characters of U(1) of a CM field: existence, weights and conjugates
- `Lib/ClassField/HeckeCharacter/AlgebraicValues` (291): Values of algebraic Hecke characters
- `Lib/ClassField/HeckeCharacter/SplitTameCharacters` (230): Splitting character on U(1), characters tamely ramified at split places, theta integrals
- `Lib/ClassField/HeckeCharacter/SplittingCharacters` (102): Splitting characters
- `Lib/ClassField/HeckeCharacter/TameModulus` (222): Characters on determinants, local values and characters tame for a modulus

**HeckeL**: Hecke L-functions

- `Lib/ClassField/HeckeL/EulerProduct` (420): Euler products over primes of a number field and densities at primes of degree one
- `Lib/ClassField/HeckeL/IdelicThetaSum` (301): Idelic theta sums over principal ideles as Riemann sums
- `Lib/ClassField/HeckeL/ContinuationAtOne` (657): Analyticity at 1 of L-functions of nontrivial Hecke characters

**Local**: Local class field theory: invariant map and Artin map

- `Lib/ClassField/Local/InvariantMap` (203): The local invariant Br(k) ≅ Q/Z and its behaviour under restriction and maps of local fields
- `Lib/ClassField/Local/ArtinMap` (682): Local and global Artin maps, algebraic Hecke characters and tame inertia

**LocalDuality**: Local Tate duality and finiteness of local cohomology

- `Lib/ClassField/LocalDuality/KummerFiniteness` (235): Index of l-th powers in a local field and finiteness of Kummer 1-cocycles
- `Lib/ClassField/LocalDuality/DualityInequality` (251): The inequality of local Tate duality for orthogonal groups of cocycles
- `Lib/ClassField/LocalDuality/CrystallineDuality` (518): Classes of Galois lattices, pairings and local duality for crystalline cocycles

**Places**: Places, Galois groups, decomposition groups and ideles

- `Lib/ClassField/Places/GaloisDefs` (126): Vocabulary of Galois theory: places, decomposition, Frobenius elements and inertia
- `Lib/ClassField/Places/ProfiniteGalois` (135): Profinite Galois groups: continuity, restriction maps and the Galois correspondence
- `Lib/ClassField/Places/DecompositionCyclotomic` (199): Decomposition and inertia groups, and cyclotomic characters at Frobenii and inertia
- `Lib/ClassField/Places/ValuationSubrings` (341): Valuation subrings over primes, primes from p-adic embeddings, and the efg formula
- `Lib/ClassField/Places/LocalFields` (445): Local fields: Frobenius, uniformisers, normalised valuation, extensions, unramified characters
- `Lib/ClassField/Places/DecompositionCompletion` (497): Decomposition groups of places above p as Galois groups of local fields in ℚ̄_p
- `Lib/ClassField/Places/Ideles` (237): Finite ideles, principal ideles and the class group; finite index of open subgroups
- `Lib/ClassField/Places/TameInertia` (269): Tame inertia, Frobenius on roots of unity over ℚ_p, the cyclotomic character, Weil pairs

### Cohomology: Cohomology of schemes

- `Lib/Cohomology/LerayHirsch` (204): The Leray–Hirsch map as a map of δ-functors, and dévissage from representable functors
- `Lib/Cohomology/TorsionTheories` (573): Tensoring degree-two classes; cohomology theories with ℓ-torsion coefficients
- `Lib/Cohomology/SmoothBaseChange` (187): Charted varieties, and smooth base change from a valuation ring to its fraction field
- `Lib/Cohomology/WoodsHole` (151): Woods Hole (half of Atiyah–Bott): maps killed under λ_h on Hodge classes are h-null. Its head has an overview of the theory.

**Etale**: Étale-type cohomology of functors of points

- `Lib/Cohomology/Etale/Basic` (581): Cohomology of functors as Ext: test rings, points, functoriality, coefficients
- `Lib/Cohomology/Etale/BijectiveComparisons` (545): Criteria for comparison maps of Ext cohomology of functors of points to be bijective
- `Lib/Cohomology/Etale/DenseSubfunctors` (344): Dense subfunctors, Mayer–Vietoris and partitions along idempotents
- `Lib/Cohomology/Etale/FilteredLimits` (542): Continuity of cohomology along filtered limits, via test rings and relatively affine maps
- `Lib/Cohomology/Etale/RelativeChains` (300): Relative chains ℤ[V]/ℤ[U]: local isomorphisms, transfer, excision and gluing
- `Lib/Cohomology/Etale/EllAdicCohomology` (117): ℓ-adic cohomology with its Galois action; finiteness and bijectivity from coefficients mod ℓ
- `Lib/Cohomology/Etale/ProperFunctors` (647): Local-to-global principle, density criteria and proper functors for cohomology on test rings

**Hodge**: Hodge cohomology, symbols and the fixed point formula

- `Lib/Cohomology/Hodge/CupProduct` (342): Pointwise tensor product of functors, total Ext with Yoneda composition, external products
- `Lib/Cohomology/Hodge/Site` (224): Hodge cohomology on algebras with free modules; universal points of charts
- `Lib/Cohomology/Hodge/DepthVanishing` (216): Vanishing of Hodge cohomology with supports below the depth, and Zariski descent
- `Lib/Cohomology/Hodge/GrothendieckSymbol` (679): Grothendieck's symbol [dT/T], cut-out loci and Hodge classes of points
- `Lib/Cohomology/Hodge/Kunneth` (250): Künneth formula: Hodge classes on X × X are sums of external products
- `Lib/Cohomology/Hodge/DiagonalClass` (181): The Hodge class of the diagonal of a variety with an atlas, with its local description
- `Lib/Cohomology/Hodge/FixedPointFormula` (694): Reduced coincidences and the fixed point formula in Hodge cohomology

**PointClass**: Hodge–Tate images of classes of points

- `Lib/Cohomology/PointClass/NoetherNormalization` (529): Projective Noether normalisation and homogeneous coordinates of embedded points
- `Lib/Cohomology/PointClass/ProjectiveSpace` (409): Projective space as a functor, and injective pull-back along Noether normalisation
- `Lib/Cohomology/PointClass/ProjectiveNonvanishing` (641): The Hodge–Tate map does not kill point classes of the projective line and space
- `Lib/Cohomology/PointClass/LinearIndependence` (449): The Hodge–Tate map keeps classes of points on a projective variety linearly independent

**ProjectiveLine**: The projective line formula and Chern class of O(1)

- `Lib/Cohomology/ProjectiveLine/ChernClass` (678): Tate module, Kummer sequence and the first Chern class of O(1) on the projective line
- `Lib/Cohomology/ProjectiveLine/PerfectLine` (318): The perfect projective line glued from two perfect discs has the cohomology of a point
- `Lib/Cohomology/ProjectiveLine/TiltedLineFormula` (721): Leray–Hirsch bases and the projective line formula for the tilted theory
- `Lib/Cohomology/ProjectiveLine/ConstantLineFormula` (315): The projective line formula for locally constant ℤ/ℓ coefficients

**ProperBaseChange**: Proper base change for ℤ/ℓ-cohomology on test rings

- `Lib/Cohomology/ProperBaseChange/LineCharts` (459): Mayer–Vietoris for two charts of a line modulo an ideal
- `Lib/Cohomology/ProperBaseChange/PlaceSpace` (344): The space of places of residue fields and its properness over the base
- `Lib/Cohomology/ProperBaseChange/SubringSplitting` (349): Splitting absolutely integrally closed subrings with a Mayer–Vietoris sequence
- `Lib/Cohomology/ProperBaseChange/Theorem` (791): Proper base change over AIC valuation rings and its consequences for ℤ/ℓ-cohomology

### Cyclotomic: Cyclotomic fields

- `Lib/Cyclotomic/Voronoi` (324): A small nonzero integer in all Stickelberger ideals via Voronoi's congruence
- `Lib/Cyclotomic/Stickelberger` (261): A weak form of Stickelberger's theorem for Gauss sums, and a family of Jacobi-type quotients
- `Lib/Cyclotomic/OddSha` (427): Detecting unramified cocycles and a uniform bound for a model of the odd part of Ш. Its head has an overview of the theory.

**Kolyvagin**: Kolyvagin cocycles, reciprocity laws and class bounds

- `Lib/Cyclotomic/Kolyvagin/DerivativeCocycles` (712): Kolyvagin's derivative cocycles from Gauss sums, for one set of primes
- `Lib/Cyclotomic/Kolyvagin/ReciprocityComponentBounds` (798): Reciprocity laws and Stickelberger and Kolyvagin bounds for odd-part cocycles

### DiscreteSeries: Discrete series of U(p,q)

- `Lib/DiscreteSeries/CuspKernel` (263): Kernels kill bounded radical-invariant functions; dilations along isotropic subspaces

**Bessel**: Bessel models of the real unitary group

- `Lib/DiscreteSeries/Bessel/Basic` (344): The real unitary group G₁, unipotent coordinates and Bessel functions
- `Lib/DiscreteSeries/Bessel/SchurBound` (444): Traces and L² bounds for Bessel functions
- `Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure` (627): Haar measures on the Bessel unipotent groups 𝖴⁰ ⊆ 𝖴 and σ-finiteness on G₁
- `Lib/DiscreteSeries/Bessel/FrameFibre` (199): Haar measure of G₁ and the fibre measure on frames

**Bruhat**: Floors and Bruhat decomposition of unitary groups

- `Lib/DiscreteSeries/Bruhat/FloorGroups` (630): Floor groups, Weyl elements and the Bessel subgroup of a split unitary group
- `Lib/DiscreteSeries/Bruhat/FloorMeasures` (760): Heisenberg elements, measures of the floors, hyperbolic bases and Plancherel at a place
- `Lib/DiscreteSeries/Bruhat/QuadricBlocks` (186): Solving the equation of a quadric in a block of coordinates
- `Lib/DiscreteSeries/Bruhat/BigCell` (260): The big cell: Bruhat decomposition of terms with non-zero leading minors, and its freeness
- `Lib/DiscreteSeries/Bruhat/FourierKernels` (382): Fourier kernels between solved measures
- `Lib/DiscreteSeries/Bruhat/ComplexPlace` (285): The place ℂ: polar coordinates, Cartan decomposition and the measure of the hyperboloid
- `Lib/DiscreteSeries/Bruhat/FloorFibre` (322): Measures of a floor below fibre measures, at the place ℂ
- `Lib/DiscreteSeries/Bruhat/SphereFibres` (94): The spheres of ℂ^κ as fibres of the standard form

**Character**: Characters and orbital integrals of discrete series

- `Lib/DiscreteSeries/Character/WeylCharacterFormula` (644): Laurent polynomials on the torus and Weyl's character and dimension formulas
- `Lib/DiscreteSeries/Character/MultiplicityOrbitalIntegral` (589): K-type multiplicities of the discrete series and orbital integrals as Laurent polynomials
- `Lib/DiscreteSeries/Character/OpenOrbitIntegral` (408): Orbital integrals of discrete series coefficients and Weyl characters of U(n)
- `Lib/DiscreteSeries/Character/FormalDegree` (391): Harish-Chandra's formula for formal degrees and stable orbital integrals

**FlenstedJensen**: Flensted-Jensen's construction of discrete series

- `Lib/DiscreteSeries/FlenstedJensen/Defs` (172): Harish-Chandra parameters, c_λ, deg_λ, e_λ and holomorphic discrete series
- `Lib/DiscreteSeries/FlenstedJensen/RightDerivatives` (308): Right derivatives and bump convolution for smooth functions on U(p,q)
- `Lib/DiscreteSeries/FlenstedJensen/FlagDensities` (528): Integrals of densities over unitary groups and over the flag variety of `K_ℂ`
- `Lib/DiscreteSeries/FlenstedJensen/CasimirEigenfunction` (513): Flensted-Jensen's integral, analyticity of c_λ and its Casimir eigenvalue
- `Lib/DiscreteSeries/FlenstedJensen/PsiKTypes` (310): First properties of c_λ and its K-types
- `Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability` (560): Decay, tail bounds and the L² model of the discrete series coefficient c_λ

**Haar**: Haar measure on unitary groups

- `Lib/DiscreteSeries/Haar/CayleyChart` (508): Cayley chart and an explicit Haar measure on the unitary group U(J)
- `Lib/DiscreteSeries/Haar/GramCoordinates` (300): Coordinates for the Gram map
- `Lib/DiscreteSeries/Haar/GramPolar` (302): The polar formula for the Gram map on bases
- `Lib/DiscreteSeries/Haar/TotalMass` (323): Haar measure on U(J): U(n) has mass one, covering bounds for norm balls
- `Lib/DiscreteSeries/Haar/GramFibre` (261): The fibre measure of the Gram map

**Holomorphic**: Holomorphic discrete series and holomorphic forms

- `Lib/DiscreteSeries/Holomorphic/MaximalCompactMinors` (170): Maximal compact subgroup, block diagonal matrices and equivariance of minors
- `Lib/DiscreteSeries/Holomorphic/HighestVectorExtension` (532): Exponentials in U(diag ε) and holomorphic extension of coefficients of highest vectors
- `Lib/DiscreteSeries/Holomorphic/ModelFunction` (459): The holomorphic model function and discrete series coefficients in the holomorphic chamber
- `Lib/DiscreteSeries/Holomorphic/PeaksAwayFromCusp` (441): The peaks of a bounded holomorphic form lie away from the cusps

**Rigidity**: Rigidity of highest vectors in the discrete series

- `Lib/DiscreteSeries/Rigidity/RepresentationsAndCasimirs` (246): gl_n-modules, unitary representations of U(J) and a Casimir bound on K-highest vectors
- `Lib/DiscreteSeries/Rigidity/HighestVectorsAndFiltration` (618): K-highest vectors, norm bounds, Casimir growth on the filtration, and analytic vectors
- `Lib/DiscreteSeries/Rigidity/KernelFixes` (421): The idempotent e_λ, the operator π(e_λ), and rigidity of highest vectors of type Λ

**Theta**: Local theta correspondence for unitary dual pairs

- `Lib/DiscreteSeries/Theta/FockDualPair` (398): Fock space oscillator actions, joint harmonics and Fischer decomposition
- `Lib/DiscreteSeries/Theta/BlockRule` (298): The block rule for corresponding parameters
- `Lib/DiscreteSeries/Theta/FockJointHarmonics` (442): Weights of matched pairs and uniqueness of joint harmonics in Fock space
- `Lib/DiscreteSeries/Theta/CasimirComparison` (289): The Casimir elements of an oscillator pair
- `Lib/DiscreteSeries/Theta/LocalCorrespondence` (499): Existence of joint harmonics, Howe's argument and the local theta correspondence

### GLn: Polynomial representations of GL(n)

- `Lib/GLn/Branching/NormBound` (488): Branching from GL(n+1) to GL(n) × GL(1): the branching vector and the norm bound
- `Lib/GLn/Branching/IntegralMap` (328): Branching from GL(n+1) to GL(n) × GL(1): integral equivariant branching maps
- `Lib/GLn/Dual` (726): Duality of integral GL(n) representations, mixed weights and the Cartan product

**SchurModule**: Schur modules and representations of GL(n)

- `Lib/GLn/SchurModule/Basic` (407): Schur modules: semi-invariants, minors, Fock pairing, Schur and Gram matrices
- `Lib/GLn/SchurModule/MinorBasis` (554): A basis of minor products for Borel semi-invariants over any ring, by induction on rows
- `Lib/GLn/SchurModule/SchurMatrix` (602): Schur matrices, the standard basis of ∇, its weights and the highest vector
- `Lib/GLn/SchurModule/TensorModel` (195): The Weyl module inside the tensors of its diagram
- `Lib/GLn/SchurModule/WeylKernel` (408): The Weyl kernel and its Gram matrix: the hook number bound, positivity, Schur's lemma
- `Lib/GLn/SchurModule/GramMatrix` (438): Fock pairing, Hermitian norm and Cartan products for the Gram matrix of the Weyl kernel
- `Lib/GLn/SchurModule/LeadingRows` (320): Fillings whose columns begin with the leading rows
- `Lib/GLn/SchurModule/SchurOrthogonality` (173): Algebraic representations of GL(n) on unitary groups: Schur orthogonality
- `Lib/GLn/SchurModule/Polarisation` (197): Irreducibility under U(n)^Φ, polarisation and averaging of determinant polynomials
- `Lib/GLn/SchurModule/SchurNorm` (227): Norm bound for Schur matrices and basic facts on the weight representations

### GaloisRep: Galois representations

- `Lib/GaloisRep/Hilbert90/TameActions` (500): Hilbert 90 for GL_n and units under tame actions on Artinian, finite or profinite rings
- `Lib/GaloisRep/Hilbert90/UnitaryGroups` (348): Hilbert 90 for unitary groups over profinite rings and for finite ideles
- `Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations` (410): Semisimple representations: conjugacy, continuity, cancellation and stable lattices
- `Lib/GaloisRep/Pseudocharacter/Pseudorepresentations` (464): Spanning criteria, limits of traces and pseudorepresentations
- `Lib/GaloisRep/KillingPolynomials` (317): Free cocharacter weights force rank n and identify killing polynomials
- `Lib/GaloisRep/WeightCongruence` (477): ℓ-adic models of algebraic forms and congruences that change the weight
- `Lib/GaloisRep/TaylorWiles` (505): Auxiliary places, base level, integral Hecke algebra and operators at the auxiliary places

**BaseChange**: Cyclic base change for definite unitary groups

- `Lib/GaloisRep/BaseChange/Defs` (101): Twisted norms, matching pairs and base change maps for unitary groups
- `Lib/GaloisRep/BaseChange/CommutingHeckeFamilies` (376): Steps E'/E of base change and commuting families of Hecke operators
- `Lib/GaloisRep/BaseChange/StepMatchingPairs` (432): Hecke-stable matching pairs for a step E'/E at split matched places
- `Lib/GaloisRep/BaseChange/GlobalRoot` (756): Idele Hasse principle, unitary roots and rationality of adelic roots up to coboundary
- `Lib/GaloisRep/BaseChange/CongruenceLevelMatching` (613): Matching unit pairs at congruence levels and at unramified places of a step
- `Lib/GaloisRep/BaseChange/TwistedTraceIdentity` (735): Twisted trace identity for a step E'/E of CM fields of prime degree
- `Lib/GaloisRep/BaseChange/PrimeDegreeTransfer` (655): Base change in prime degree for definite U(n): a weak base change eigenform
- `Lib/GaloisRep/BaseChange/IwahoriEigenforms` (556): Hilbert 90 for the pro-p Iwahori group and base change of Iwahori eigenforms
- `Lib/GaloisRep/BaseChange/ShintaniLift` (286): Base change at an inert place carries a label to its Shintani lift

**LocalGlobal**: Local-global compatibility at split places

- `Lib/GaloisRep/LocalGlobal/LocalFormTypes` (227): Local GL_N(E_w)-action on forms, parahoric types and labels at a split place
- `Lib/GaloisRep/LocalGlobal/IwahoriCompatibility` (488): Local-global compatibility at split places for Iwahori eigencharacters and parahoric types
- `Lib/GaloisRep/LocalGlobal/LabelCompatibility` (322): Tame exponents of inertia and local-global compatibility for labelled forms

**Main**: Galois representations for definite unitary eigenforms

- `Lib/GaloisRep/Main/SelmerModules` (138): Selmer modules, Tate twists, components of cocycles and places above a prime
- `Lib/GaloisRep/Main/DivisibleSelmerModules` (90): Selmer modules with divisible coefficients
- `Lib/GaloisRep/Main/Defs` (156): Weights, Hecke polynomials, eigenforms and the filter of most Frobenii
- `Lib/GaloisRep/Main/LocalConditions` (279): Local conditions on ℓ-adic Galois representations and their passage to retracts
- `Lib/GaloisRep/Main/QuadraticStep` (378): Split places over ℚ(√−d) and quadratic steps with prescribed splitting
- `Lib/GaloisRep/Main/CuspidalTypes` (370): Cuspidal types, multiplicity-free sums and the Hodge–Tate cocharacter
- `Lib/GaloisRep/Main/AttachedRepresentations` (225): Attached Galois representations: traces, characteristic polynomials and rank one
- `Lib/GaloisRep/Main/SeedRepresentation` (634): Seed representations: odd rank, a cuspidal type and free jumps
- `Lib/GaloisRep/Main/SplitCase` (478): Attached Galois representations in odd rank: the split case
- `Lib/GaloisRep/Main/OddRank` (328): Attached Galois representations in odd rank and their descent along weak base change
- `Lib/GaloisRep/Main/ThetaLift` (324): Theta lift of an algebraic form to a larger definite unitary group and its Hecke polynomials
- `Lib/GaloisRep/Main/AllRanks` (478): Isotypic spaces of eigenforms and attached Galois representations in every positive rank. Its head has an overview of the theory.

### General: General lemmas

- `Lib/General/Combinatorics` (257): The q-binomial theorem, fibre sums, and Schur polynomials in the coefficients
- `Lib/General/Topology` (114): Open subgroups, a tube lemma, and procyclic images of ℓ-adic characters

**Algebra**: Commutative algebra, cohomology and p-adic algebra

- `Lib/General/Algebra/AbsIntegrallyClosed` (82): Absolutely integrally closed rings and their stability properties; Frobenius powers
- `Lib/General/Algebra/AdicCompletion` (414): Adic completeness: p-adic tools, extension by continuity, topological bases
- `Lib/General/Algebra/SeriesCongruences` (264): Power series with prime power exponents, congruences and convergent sums
- `Lib/General/Algebra/CartanMap` (423): Higman's criterion, dévissage and multiplicative functions on finite modules (Cartan map)
- `Lib/General/Algebra/LongExactSequences` (328): Long exact sequences, four and five lemmas, and Ext with disjoint unions and products
- `Lib/General/Algebra/MultivariatePolynomials` (286): Multivariate polynomials: cost of vanishing, homogenization, Nullstellensatz, Hensel
- `Lib/General/Algebra/ResidueSums` (58): Sums of residues at simple real poles
- `Lib/General/Algebra/CohomologyBaseChange` (158): Flat base change in functor cohomology, and the base change adjunction for algebras
- `Lib/General/Algebra/IntegralPowerSeries` (169): Integral power series over ℂ_p: jets, the chain rule and the exponential
- `Lib/General/Algebra/PerfectAlgebras` (350): Perfect algebras, étale algebras over perfect rings, and constant Laurent polynomials
- `Lib/General/Algebra/FittingIdealsAndLengths` (424): Relations, relative lengths and Fitting ideals for Selmer group estimates
- `Lib/General/Algebra/BlockFittingBound` (115): A matrix of relations with small block determinant valuation
- `Lib/General/Algebra/SeriesBounds` (271): Integrality of exponentials, logarithms and roots of power series
- `Lib/General/Algebra/SharpMinors` (181): Maximal minors and lengths
- `Lib/General/Algebra/LevelModulus` (229): Level moduli, residue data as Schwartz–Bruhat functions, and descent in positive degree

**Analysis**: Real and complex analysis

- `Lib/General/Analysis/FiniteFourier` (148): Orthogonality, Fourier inversion and matrix Gauss sums over a finite ring
- `Lib/General/Analysis/GaussianIntegral` (146): Matrix norm estimates, the Ostrowski–Taussky inequality, and the complex Gaussian integral
- `Lib/General/Analysis/FourierTransforms` (207): Fourier inversion for periodic functions and decay of Fourier transforms
- `Lib/General/Analysis/HolomorphicIntegrals` (456): Strong operator integrals, analyticity of parameter integrals, and Hua's integral bound
- `Lib/General/Analysis/PackingAndSobolev` (173): Packing bounds for separated points and Sobolev trace inequalities
- `Lib/General/Analysis/MeanValueAndTaylor` (141): Circle means, Taylor series at zero, a power bound, and smooth matrix operations

**Geometry**: Schemes through points, line bundles and charts

- `Lib/General/Geometry/LineBundles` (618): Line bundles on schemes via ring-valued points: descent and the Picard group
- `Lib/General/Geometry/ProjectiveSpace` (529): Projective space, linear systems and projective embeddings, with Segre and Veronese
- `Lib/General/Geometry/DenseComplexPoints` (280): Dense families of complex points: reduced closures, separation of maps, and arcs
- `Lib/General/Geometry/GeometricPoints` (287): Geometric points, specialisation, separating products and integral abelian varieties
- `Lib/General/Geometry/EtaleCharts` (632): Functors of points on algebras: open subfunctors, étale charts, atlases, charted schemes
- `Lib/General/Geometry/PointsOfProperSchemes` (342): Functors of points of proper schemes: closed loci, atlases and descent of relations
- `Lib/General/Geometry/SerreTheorem` (248): Absolute Frobenius, Serre's theorem on sections of powers, and projective embeddings
- `Lib/General/Geometry/GaloisCovers` (530): Complex points over countable rings, Zariski generic members and Galois coverings
- `Lib/General/Geometry/SmoothnessCriterion` (337): Smoothness near an arc from an immersive generic family and a bound on the tangent space

**Groups**: Matrix groups, characters and group algebras

- `Lib/General/Groups/CongruenceSubgroups` (254): Integral, congruence and unitary matrix groups over a ring, with their topology
- `Lib/General/Groups/IndexOfProduct` (9): The index of a product of subgroups is the product of the indices
- `Lib/General/Groups/BesselGroups` (138): Block triangular groups, unipotent Bessel groups, Levi and parahoric subgroups
- `Lib/General/Groups/ProfiniteCharacters` (234): ℚ/ℤ, characters of profinite groups, and extension of homomorphisms
- `Lib/General/Groups/CharacterTheory` (495): Characters of finite groups: averages, virtual characters and central projections

**LinearAlgebra**: Linear algebra and matrix analysis

- `Lib/General/LinearAlgebra/TensorChains` (173): Chains of linear maps, tensor products of their data, and separation by forms
- `Lib/General/LinearAlgebra/Eigenvalues` (507): Eigenvalues: traces of powers, common eigenvectors, Amitsur's theorem, Sylvester's law
- `Lib/General/LinearAlgebra/HermitianMatrices` (216): Determinants of positive semidefinite matrices, principal minors and hermitian involutions
- `Lib/General/LinearAlgebra/IntegralLattices` (455): Integral matrices over subrings: Smith normal form, Gelfand's condition and lattices
- `Lib/General/LinearAlgebra/MatricesNearIdentity` (262): Matrices near the identity: Jacobi's formula and norm estimates
- `Lib/General/LinearAlgebra/MinorProducts` (296): Products of principal minors, Fischer's inequality and the Cauchy–Binet formula
- `Lib/General/LinearAlgebra/GramDeterminant` (78): Gram determinants
- `Lib/General/LinearAlgebra/MatrixPolynomials` (125): Minors, polynomials of matrices and twisted norms
- `Lib/General/LinearAlgebra/IdempotentRadical` (123): The unipotent radical attached to an idempotent matrix
- `Lib/General/LinearAlgebra/HermiteForm` (139): Hermite forms over valuation pairs and integral matrices over valued fields
- `Lib/General/LinearAlgebra/MatrixNormBounds` (80): Auerbach's lemma, ultrametric matrix bounds and Gram norms
- `Lib/General/LinearAlgebra/PartnerAlgebra` (207): Rows and columns of integral matrices, primitive matrices and the law of partners
- `Lib/General/LinearAlgebra/PolarDecomposition` (122): Gram–Schmidt, tight frames, polar decomposition in U(p,q), forms representing one
- `Lib/General/LinearAlgebra/BlockEmbeddings` (241): Extending columns, block matrices and block embeddings

**Measure**: Measure theory, Haar measures and integration

- `Lib/General/Measure/FibreMeasure` (149): Measures below a fibre measure
- `Lib/General/Measure/IdempotentKernel` (121): Fubini and convolution lemmas; idempotent kernels
- `Lib/General/Measure/HaarNormalisation` (126): Uniqueness of Haar measure, integrals over subgroups and Gaussian normalisation of volumes
- `Lib/General/Measure/IntegralOperators` (293): Product measures, layer cake bounds, cocompact subgroups and L² bounds of integral operators
- `Lib/General/Measure/HaarModulus` (275): Pushforward of Haar measures, the modulus of GL_n and the generalised index
- `Lib/General/Measure/QuadricDisintegration` (408): Measures on hermitian quadrics: existence and uniqueness of disintegrations

**NumberTheory**: Number fields, local fields, adeles and lattices

- `Lib/General/NumberTheory/FrobeniusOrbits` (146): Frobenius orbits of roots over finite fields and residue fields at self-conjugate places
- `Lib/General/NumberTheory/EmbeddingsAndDifferent` (158): Embeddings, differents and the maximal real subfield of a CM field
- `Lib/General/NumberTheory/ImaginaryQuadraticField` (341): The imaginary quadratic field ℚ(√−d): characters, Frobenius and splitting of primes
- `Lib/General/NumberTheory/SUnitsAndClassNumber` (157): Principal ideal powers, S-units and a class number bound
- `Lib/General/NumberTheory/CMFields` (115): Criteria for CM fields
- `Lib/General/NumberTheory/CoefficientRings` (119): Coefficient rings of ℓ-adic lattices, and length versus cardinality of modules
- `Lib/General/NumberTheory/LatticeCovolumes` (532): Lattice indices, primitive matrices, Jacobi's identity and covolumes of fundamental domains
- `Lib/General/NumberTheory/PadicLimitsValuation` (202): Algebraicity from ℓ-adic bounds, roots of unity as limits, and the ℓ-adic valuation
- `Lib/General/NumberTheory/GaussValuation` (325): The Gauss valuation of a polynomial over the ring of integers of ℚ̄_ℓ
- `Lib/General/NumberTheory/LargeResidueField` (113): Coefficient rings with a large residue field
- `Lib/General/NumberTheory/CoefficientInclusion` (52): Coefficient rings inside the ring of all integral elements

### LocalGL: GL(n) over finite and local fields

- `Lib/LocalGL/SphericalChainLemma` (446): Chains of roots of the Hecke polynomial of a spherical vector

**Green**: Green's characters of general linear groups over finite fields

- `Lib/LocalGL/Green/HallAlgebra` (659): Hall algebra of class functions: induction product, Mackey formula, Frobenius reciprocity
- `Lib/LocalGL/Green/CuspidalFunctions` (473): Cuspidal class functions on GL_n over a finite field: μ, supports, values, inner products
- `Lib/LocalGL/Green/TauFunctions` (474): Green's characters of GL_n over a finite field: θ_x, τ_P, labels and their degrees
- `Lib/LocalGL/Green/LabelCharacters` (393): Label characters Ξ_c: orthonormality, central idempotents and twisting by χ∘det

**Iwahori**: Iwahori subgroups, Hecke operators and exponents

- `Lib/LocalGL/Iwahori/ParahoricStructure` (478): Parahoric and pro-p Iwahori subgroups of GL_n over a local field and U_t operators
- `Lib/LocalGL/Iwahori/QuadraticRelation` (294): Quadratic relation and injectivity of U_t at pro-p Iwahori level
- `Lib/LocalGL/Iwahori/HeckeDegrees` (435): Iwahori degrees, partial Hecke sums and Satake's formula
- `Lib/LocalGL/Iwahori/SortedExponents` (602): Sorted exponents at pro-p Iwahori level
- `Lib/LocalGL/Iwahori/SphericalExponents` (397): Exponents that survive on spherical vectors, and a Hecke operator on parahoric eigenvectors

**Shintani**: Shintani descent and lifting over finite fields

- `Lib/LocalGL/Shintani/CosetRootChoice` (351): Root choices in a coset, induction, and extension of invariant characters
- `Lib/LocalGL/Shintani/CosetDescent` (525): Descent of class functions along a coset and lifts from GL_n(k') ⋊ Gal(k'/k)
- `Lib/LocalGL/Shintani/LiftingGreenCharacters` (498): Shintani lifting of Green's characters along extensions of prime degree

### PadicComparison: p-adic comparison theorems

- `Lib/PadicComparison/Completion` (317): Derived completeness, adic approximation of comparisons and completed base change
- `Lib/PadicComparison/ToricTower` (508): Wang sequence on C × Bℕ, lines, and root systems of units via periodic sequences
- `Lib/PadicComparison/CrystallineFrobenius` (539): Crystallinity of p-adic cohomology of charted proper schemes and Frobenius congruences. Its head has an overview of the theory.

**Crystalline**: The crystalline comparison theorem

- `Lib/PadicComparison/Crystalline/DividedPowerEnvelope` (385): Divided power envelopes, lifts modulo divided powers, and one divided power variable
- `Lib/PadicComparison/Crystalline/ComparisonMap` (793): Crystalline comparison: bijectivity on étale charts and spanning of period cohomology

**Descent**: p-adic tests and almost v-descent

- `Lib/PadicComparison/Descent/TestCategory` (356): Divided power ideal, p-adic test rings, tilt, Witt vectors and reduction modulo p
- `Lib/PadicComparison/Descent/TestCovers` (362): p-adic tests: tilts, Fontaine's map, covers by tests and flat base change
- `Lib/PadicComparison/Descent/AlmostDescent` (594): Almost coefficients, v-descent for perfect algebras and acyclicity of tilt points

**Duality**: Duality and good pairs for compared theories

- `Lib/PadicComparison/Duality/LineIntegration` (605): Integration over ℙ¹, compared cohomology theories, and moving kernel classes in (ℙ¹)^d
- `Lib/PadicComparison/Duality/GoodPairs` (480): Good pairs: excision, Thom retraction and Alexander duality for principal opens

**HodgeTate**: The Hodge–Tate map and Hodge–Tate weights

- `Lib/PadicComparison/HodgeTate/ExtCocycles` (204): Ext¹ classes of cocycles of functors, and contraction on exterior algebras
- `Lib/PadicComparison/HodgeTate/GenericFibre` (283): The ring R[1/p] of a p-adic test and the square-zero extension W(R♭)[1/p]/(ker θ)²
- `Lib/PadicComparison/HodgeTate/Map` (506): The Hodge–Tate maps λ_h on pairs (S, M): construction, properties and restriction
- `Lib/PadicComparison/HodgeTate/GaloisWeight` (145): Galois twists and the weight of the Hodge–Tate map
- `Lib/PadicComparison/HodgeTate/PeriodMap` (219): The period map for ℓ-adic cohomology on p-adic tests, and Hodge–Tate weights

**Primitive**: The primitive comparison theorem

- `Lib/PadicComparison/Primitive/PeriodCoefficients` (417): Tilts and period coefficients of p-adic tests: products, comparisons, theories
- `Lib/PadicComparison/Primitive/Periods` (200): The primitive comparison with period coefficients
- `Lib/PadicComparison/Primitive/ComparisonTheorem` (251): The primitive comparison theorem and finiteness of p-adic cohomology

### PadicHodge: p-adic Hodge theory

- `Lib/PadicHodge/TateSen` (356): Tate's vanishing theorem, Hodge–Tate elimination and the filtration of B_dR
- `Lib/PadicHodge/ArtinSchreierSequence` (300): W(𝔪^♭), the diagonal tensor module W(C^♭) ⊗ T and the Artin–Schreier sequence
- `Lib/PadicHodge/BlochKato` (567): Bloch–Kato crystalline cocycles: reduction modulo p^m, rank and vanishing
- `Lib/PadicHodge/RadiusLemma` (367): The radius lemma: after Frobenius a frame is a constant basis times a unit over A
- `Lib/PadicHodge/Characters` (650): p-adic avatars of Hecke characters and local conditions for twists and characters

**Crystalline**: Crystalline representations and Hodge–Tate jumps

- `Lib/PadicHodge/Crystalline/Basic` (330): Crystalline and potentially crystalline representations and admissibility
- `Lib/PadicHodge/Crystalline/HodgeTateForms` (103): Semilinear forms of given weight: independence, finiteness, and jumps read off a basis
- `Lib/PadicHodge/Crystalline/HodgeTateJumps` (552): Hodge frames and Hodge–Tate jumps under operations on representations
- `Lib/PadicHodge/Crystalline/FixedRatios` (258): Bounded poles, φ-fixed elements of B_max, and ratios of periods fixed near 1
- `Lib/PadicHodge/Crystalline/Regularity` (470): Regularity of B_max, closure of admissibility, and crystalline descent from inertia

**Kisin**: Charts, period matrices and Kisin modules

- `Lib/PadicHodge/Kisin/Charts` (477): Power series charts Λ⟦z⟧ in A_inf: Weierstrass division and fixed elements
- `Lib/PadicHodge/Kisin/Bicommutant` (360): The ring S_B of a chart and extension of S-linear maps of A_inf to B^+
- `Lib/PadicHodge/Kisin/KummerChartExistence` (260): Witt coefficients, the Frobenius group action and existence of Kummer charts
- `Lib/PadicHodge/Kisin/PeriodMatrixBasis` (704): Period matrices over a chart: lattice bases and existence for crystalline lattices
- `Lib/PadicHodge/Kisin/KummerChartDeRham` (293): Kummer charts: the different, the primes φ^a E of A_inf and their images in B_dR
- `Lib/PadicHodge/Kisin/PeriodMatrixFrame` (335): The frame theorem for a period matrix, with Frobenius and Galois action on the frame
- `Lib/PadicHodge/Kisin/Modules` (368): Kisin modules of Kummer charts: lattices with jump sets, letter projectors, invariant forms
- `Lib/PadicHodge/Kisin/FrameTheorem` (666): The frame theorem for Kisin modules and stability under normalising Galois elements. Its head has an overview of the theory.

**Limit**: Limits of crystalline and Galois representations

- `Lib/PadicHodge/Limit/CrystallineLimit` (459): Uniform period bounds and limits of crystalline lattices with bounded jumps
- `Lib/PadicHodge/Limit/TraceLimit` (606): Hodge–Tate jumps with bounded denominators and local conditions at limits of traces. Its head has an overview of the theory.

**PeriodRings**: Fontaine's period rings A_inf, A, B and B_dR

- `Lib/PadicHodge/PeriodRings/AxTheorem` (309): Tilting, Fontaine's θ, the ring O_C and Ax's theorem on Galois invariants in ℂ_p
- `Lib/PadicHodge/PeriodRings/Ainf` (605): The ring A_inf, the elements ε, μ, τ, ξ, the kernel of θ and adic completeness
- `Lib/PadicHodge/PeriodRings/CrystallineRings` (689): The period rings A, B⁺, B and B_dR⁺: θ, Frobenius, domains and contraction
- `Lib/PadicHodge/PeriodRings/DeRhamPeriods` (242): The cyclotomic action on μ, the period t, and the de Rham field B_dR

### Shimura: Moduli of abelian varieties

- `Lib/Shimura/ComplexTheta/AppellHumbertData` (453): Theta functions on complex tori: Appell–Humbert data and factors of automorphy
- `Lib/Shimura/ComplexTheta/DimensionFormula` (510): Theta functions on complex tori: dimension formula, base points, multipliers
- `Lib/Shimura/ThetaGroup` (314): Lifts of morphisms to sections of line bundles, and theta structures on abelian schemes
- `Lib/Shimura/ArcExtension` (387): Uniformisations over an arc: theta coordinates, Weil pairing and extension of maps
- `Lib/Shimura/Eigenspace` (504): Eigenquotients for Hecke eigensystems and the Galois representations they cut out. Its head has an overview of the theory.

**AbelianScheme**: Abelian schemes over a base and their isogenies

- `Lib/Shimura/AbelianScheme/Basic` (267): Abelian schemes: base change, finite kernels and constant functions
- `Lib/Shimura/AbelianScheme/Pairings` (238): Pairings of line bundle classes on abelian schemes and their fpqc descent
- `Lib/Shimura/AbelianScheme/IsogenyFlatness` (187): Isogenies: factorisation of homomorphisms, finiteness and flatness
- `Lib/Shimura/AbelianScheme/TangentCoordinates` (351): Étale coordinates at zero, infinitesimal points and unramified torsion

**CongruenceRelation**: The congruence relation at split places

- `Lib/Shimura/CongruenceRelation/KernelReduction` (580): Reduction of isogeny kernels: Cartier density, the tangent line and torsion sections
- `Lib/Shimura/CongruenceRelation/EichlerShimura` (125): The congruence relation and the trivial action of inertia on ℓ-adic cohomology
- `Lib/Shimura/CongruenceRelation/HeckeNeighbours` (741): Hecke elements on adelic torsion and reductions of Frobenius twists of Hecke neighbours

**Deformation**: First-order deformations and the tangent space bound

- `Lib/Shimura/Deformation/TangentCount` (368): Counting w-torsion points bounds a space of natural semilinear functions by n − 1
- `Lib/Shimura/Deformation/TangentBound` (572): Drinfeld lifting over k[ε] and a bound on the tangent space of the moduli scheme

**GoodReduction**: Good reduction of theta tori

- `Lib/Shimura/GoodReduction/TorsionSizes` (295): Sizes of theta functions at torsion points: products, bounds and shift bounds
- `Lib/Shimura/GoodReduction/GaussSums` (265): Hermitian tori with multiplications, Gauss sums and unfolding of the Poincaré kernel
- `Lib/Shimura/GoodReduction/MultiplicativeNorm` (694): Good reduction of theta tori from shift bounds on kernels of multiplications

**HeckeTower**: Hecke operators on a tower of Kuga–Sato varieties

- `Lib/Shimura/HeckeTower/HeckeData` (576): Hecke elements in group rings, marked triples, local terms and neat levels
- `Lib/Shimura/HeckeTower/Model` (562): Properties of a Kuga–Sato tower, Hecke operators at split places, torsion counts and levels

**IntegralModel**: Construction of the integral model of the moduli tower

- `Lib/Shimura/IntegralModel/PELDataExistence` (334): Existence of PEL data at levels good at all safe places, with the form ξ and a Lagrangian
- `Lib/Shimura/IntegralModel/UniversalFamily` (680): The universal family: models along arcs, rigid fibres and points of linear data
- `Lib/Shimura/IntegralModel/BallImmersion` (319): Balls immerse; holomorphy, arcs and complex points of the covers
- `Lib/Shimura/IntegralModel/TowerExistence` (321): Existence of the model: the tower of Kuga–Sato covers with its congruence relation

**ThetaModuli**: Moduli of abelian schemes embedded by theta coordinates

- `Lib/Shimura/ThetaModuli/FlatClosure` (639): Flat families of ideals cut out by points and the flat closure of theta points
- `Lib/Shimura/ThetaModuli/PELThetaTori` (677): PEL data, the adelic Riemann form and theta coordinates of polarised period maps
- `Lib/Shimura/ThetaModuli/ThetaFamilyRigidity` (346): Theta objects of PEL moduli problems, their pull-backs, and rigidity over local rings
- `Lib/Shimura/ThetaModuli/FamilyFromPoints` (805): Linear systems and theta families from dense complex points carrying theta tori
- `Lib/Shimura/ThetaModuli/UniversalFamily` (331): Existence of the universal theta family over a smooth projective base

**ThetaNormality**: Integral theta functions and their good reduction

- `Lib/Shimura/ThetaNormality/NormalGeneration` (444): Orthogonality of theta translates and balls of integral theta functions
- `Lib/Shimura/ThetaNormality/RiemannRelation` (494): Riemann's theta relation and the reduction of theta functions at a valuation

**TraceFormula**: Trace formula on the definite side and its comparison

- `Lib/Shimura/TraceFormula/TestFunction` (257): Test vectors, and the regular Hecke element that does not kill them
- `Lib/Shimura/TraceFormula/DefiniteTrace` (374): Trace formula for algebraic forms, finiteness of signed frame classes, the definite side
- `Lib/Shimura/TraceFormula/MarkedDefiniteSums` (552): For a function with a cuspidal type at one place, marked and definite orbit sums agree

**Transfer**: Transfer of Hecke eigensystems via the Lefschetz formula

- `Lib/Shimura/Transfer/MarkedPairs` (124): Eigenline reflections of a separable matrix, and the term of the count at a marked triple
- `Lib/Shimura/Transfer/Lefschetz` (371): h-null Hecke elements and the Lefschetz formula as a sum over marked pairs
- `Lib/Shimura/Transfer/WeightOccurs` (493): Coefficient systems from weights and the degrees where Hecke eigensystems occur

**Uniformisation**: Complex uniformisation of abelian varieties and moduli points

- `Lib/Shimura/Uniformisation/AdelicFrames` (327): Adelic frames over a CM field, torsion classes, period lattices and period maps
- `Lib/Shimura/Uniformisation/HolomorphicFamilies` (590): Holomorphic families of complex points, jets, uniformisations and theta coordinates
- `Lib/Shimura/Uniformisation/AppellHumbert` (348): Existence in Appell–Humbert: projective embeddings are given by theta functions
- `Lib/Shimura/Uniformisation/LieExponential` (570): Exponential of compact commutative Lie groups and uniformisation of abelian varieties
- `Lib/Shimura/Uniformisation/BallModel` (671): Period signatures, analytic families of theta tori and the ball chart of moduli points
- `Lib/Shimura/Uniformisation/TorusModel` (514): Objects modelled on complex tori and their homomorphisms as rational matrices
- `Lib/Shimura/Uniformisation/ModelExists` (314): Every full complex object is modelled on a point (g, ℓ)

### SiegelWeil: Siegel–Weil and Rallis formulas

- `Lib/SiegelWeil/NeighbourLattices` (472): Neighbours of the standard lattice
- `Lib/SiegelWeil/Mass` (292): Masses of definite hermitian lattices and ideal zeta bounds for adelic Gauss sums
- `Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients` (447): Vacuum coefficients, coset representatives and the weight of steps through neighbours
- `Lib/SiegelWeil/UnramifiedSeries/RallisSeries` (429): The series of translates weighted by the coefficients of the vacuum
- `Lib/SiegelWeil/RallisInner/Doubling` (435): Doubling: clean data, the doubling identity and the inner product formula
- `Lib/SiegelWeil/RallisInner/SharpData` (641): Rallis' inner product formula for sharp data and injectivity of the theta lift
- `Lib/SiegelWeil/Reproduction` (288): Holomorphic Fock vectors and a reproducing formula by theta lifts

**Formula**: The Siegel–Weil formula for split hermitian spaces

- `Lib/SiegelWeil/Formula/LagrangianZeroTerms` (622): Lagrangians, zero terms of the Weil representation and vanishing of dominated functionals
- `Lib/SiegelWeil/Formula/StrongApproximation` (125): Strong approximation and constancy of automorphic functions in equal rank
- `Lib/SiegelWeil/Formula/WeilRange` (571): Siegel sets and the Siegel–Weil formula in Weil's range

**OneVector**: Siegel's formula for representation numbers

- `Lib/SiegelWeil/OneVector/FinitePlaceDensity` (489): Local measure bounds and local densities at a finite place
- `Lib/SiegelWeil/OneVector/ResidueClasses` (42): Classes modulo a lattice at a finite place
- `Lib/SiegelWeil/OneVector/ClassGaussSums` (172): Gauss sums of classes modulo a lattice at a finite place
- `Lib/SiegelWeil/OneVector/SemilocalDensityBounds` (156): Bounds for local densities at finitely many finite places
- `Lib/SiegelWeil/OneVector/StandardQuadrics` (114): The quadrics of the standard form at a finite place
- `Lib/SiegelWeil/OneVector/SiegelClassSum` (649): Siegel–Weil for one vector, Siegel's class sum formula and the ratio of masses

**SingularForms**: Fourier coefficients and singular automorphic forms

- `Lib/SiegelWeil/SingularForms/CentreCoefficients` (514): Fourier coefficients along the centre of a unipotent radical and their partial means
- `Lib/SiegelWeil/SingularForms/UnimodularCoefficients` (539): Singular forms governed by unimodular coefficients

**Tower**: The theta tower and constant terms of theta integrals

- `Lib/SiegelWeil/Tower/PrincipalIdeles` (56): Principal ideles and a majorant on the complex torus
- `Lib/SiegelWeil/Tower/LineTerms` (205): Coordinates on a line parabolic and Poisson's formula for terms along lines
- `Lib/SiegelWeil/Tower/ConstantTerm` (482): The constant term of a theta integral, unfolded along isotropic lines
- `Lib/SiegelWeil/Tower/LineGaussSums` (408): Standard partners, shear invariance, Gauss sums along lines and coefficients of lifts
- `Lib/SiegelWeil/Tower/RealConeIntegral` (161): The real cone integral
- `Lib/SiegelWeil/Tower/FiniteTateIntegral` (226): Products of `L`-values and Tate's integral at the finite places
- `Lib/SiegelWeil/Tower/TestVector` (261): The test vector of the zeta integral
- `Lib/SiegelWeil/Tower/LargeSideConstantTerm` (609): Removing a plane: the constant term on the side of the large space
- `Lib/SiegelWeil/Tower/FunctionalEquation` (302): The functional equation of the `L`-function of a tamely ramified character

### Weil: The Weil representation and theta lifts

- `Lib/Weil/TameGaussSum` (165): Tame local characters, integral frames and the local Gauss sum
- `Lib/Weil/Lift` (609): Theta lifts of forms: products of minors, edges, arrows between spaces of forms
- `Lib/Weil/Seesaw` (446): Theta lifts for families of characters over a real edge and the seesaw of periods

**CompactLift**: Theta lifts between definite unitary groups

- `Lib/Weil/CompactLift/ThetaKernelDefs` (255): The jet matrix of a definite pair is a kernel for algebraic forms
- `Lib/Weil/CompactLift/DefiniteThetaLift` (220): Theta lifts between definite unitary groups and algebraic lifts by jets

**Construction**: Construction of the adelic Weil representation

- `Lib/Weil/Construction/HeisenbergModel` (425): Heisenberg cocycles, vacua, the reproducing model and Schur's lemma
- `Lib/Weil/Construction/WeilOperators` (541): Weil operators, orthogonal sums and transport of the reproducing model
- `Lib/Weil/Construction/WeilData` (87): Splitting characters, Weil data, and the adelic Heisenberg cocycle and vacuum
- `Lib/Weil/Construction/FiniteMultiplier` (600): Finite Heisenberg datum, its lattice vacuum and the finite multiplier
- `Lib/Weil/Construction/FiniteCocycle` (300): The finite cocycle as a finite Gauss sum, and its triviality
- `Lib/Weil/Construction/AdelicRepresentation` (565): The adelic Weil representation on 𝒮(V) and its theta functional
- `Lib/Weil/Construction/VacuumProjections` (594): Vacuum projections and the finite part of the Weil representation
- `Lib/Weil/Construction/ProductsAndTransport` (206): Products of data along a splitting of coordinates, and changes of coordinates
- `Lib/Weil/Construction/ThetaJets` (149): Jet series of theta functions and translation by rational vectors
- `Lib/Weil/Construction/CanonicalTheta` (123): Independence of the theta functional of the chosen group element; transport and sums
- `Lib/Weil/Construction/ThetaDictionary` (378): The dictionary between vectors and theta functions
- `Lib/Weil/Construction/FourierInversion` (302): Fourier inversion for theta functions

**DualPair**: Dual pairs of unitary groups and their theta kernels

- `Lib/Weil/DualPair/Kronecker` (25): The action x ↦ hxg⁻¹ on matrices as a map of unitary groups
- `Lib/Weil/DualPair/Defs` (362): Hom(S,T), the Weil representation and theta kernel of a pair, and data modulo an ideal
- `Lib/Weil/DualPair/ShortIsotropicVectors` (406): Short isotropic vectors and means of theta functionals over isotropic subspaces
- `Lib/Weil/DualPair/WeilAction` (470): Laws of the Weil action of a pair: translations, real points, levels, rational maps
- `Lib/Weil/DualPair/FiniteAction` (297): Weil representation of unitary pairs: finite action, sums, negation and change of point
- `Lib/Weil/DualPair/MixedModel` (274): Mixed models and zero terms of a pair with one split space: Levi and radical laws
- `Lib/Weil/DualPair/ThetaLiftConvergence` (352): Growth of theta kernels and convergence of theta lifts
- `Lib/Weil/DualPair/GaloisLaw` (243): Semilinear maps intertwining the Weil action up to σΔ/Δ
- `Lib/Weil/DualPair/KernelDecay` (403): Rapid decay of theta kernels of unitary dual pairs under support conditions
- `Lib/Weil/DualPair/KernelLaws` (355): Theta kernels of unitary pairs modulo an ideal: formal laws and seesaw identities
- `Lib/Weil/DualPair/Flip` (362): Flipping a dual pair by adjoints: Weil actions and theta kernels modulo ideals
- `Lib/Weil/DualPair/ThetaIntegrals` (302): Terms of theta kernels at rational matrices and basic laws of theta integrals
- `Lib/Weil/DualPair/HolomorphicData` (172): Holomorphic data, functions of a level, and theta kernels modulo 𝔪 as level multipliers
- `Lib/Weil/DualPair/TwoEdges` (170): Two edges V → V′ → V″ joined into one datum of the pair (V′, V⁻ ⊕ V″)

**Fock**: The Fock model of the real Weil representation

- `Lib/Weil/Fock/Basic` (548): The Fock model of the Weil representation of U(ε) at a real place
- `Lib/Weil/Fock/WeightedNorms` (406): Moments on Fock space, approximation by polynomial vectors, bounds for functionals
- `Lib/Weil/Fock/PolynomialVectors` (280): Polynomial vectors in Fock space: inner product, density and Weil derivative
- `Lib/Weil/Fock/OscillatorPair` (363): Harmonic matrix coefficients of the Weil representation and oscillator pairs on matrices

**MixedModel**: Mixed Schrödinger models, zero terms and named data

- `Lib/Weil/MixedModel/FockSections` (269): Mixed Schrödinger–Fock models and rapid sections with prescribed values
- `Lib/Weil/MixedModel/SchwartzBruhat` (404): Schwartz–Bruhat functions on a set of places and the Schrödinger model there
- `Lib/Weil/MixedModel/IsotropicSplitting` (719): Hyperbolic space and splittings of a hermitian space along isotropic subspaces
- `Lib/Weil/MixedModel/NamedData` (353): Data named by Schwartz–Bruhat functions: Heisenberg laws, transport, Weil action
- `Lib/Weil/MixedModel/RealTheta` (355): Real data, the entire theta function, and the real vacuum in the mixed model
- `Lib/Weil/MixedModel/ZeroTerm` (502): Zero term and mixed model of the Weil representation: slices and θ as a sum of slices
- `Lib/Weil/MixedModel/ThetaInvariance` (407): Mixed model of the Weil representation: Levi intertwining and invariance of θ
- `Lib/Weil/MixedModel/AdaptedSplitting` (177): Adapted splittings: hyperbolic polarisation, Hom spaces, composition and stages
- `Lib/Weil/MixedModel/Slices` (404): Real, named and finite slices of data in the mixed model of an adapted splitting
- `Lib/Weil/MixedModel/TargetZeroTerm` (224): Zero terms of the mixed models of the Weil representation at the real places

**Periods**: Bessel periods and unfolding of theta integrals

- `Lib/Weil/Periods/Grading` (495): Graded hermitian spaces X ⊕ J_s, Bessel subgroups, the map T, and c_λ in a frame
- `Lib/Weil/Periods/PointLattice` (286): The lattice of a finite point of a graded space
- `Lib/Weil/Periods/GradedLattice` (220): Iwasawa decomposition for the flag of the grades
- `Lib/Weil/Periods/LatticeBounds` (130): Finitely many orbits of lattices satisfy the bounds
- `Lib/Weil/Periods/StringPowers` (186): The string of a graded space as the powers `𝔢 ^ i`
- `Lib/Weil/Periods/BesselIntegral` (557): Integrals over the Bessel subgroup and the orbits surviving unipotent twists
- `Lib/Weil/Periods/Equivariant` (261): The character `ψ_U` and the function `𝒲_φ`
- `Lib/Weil/Periods/ConstantTerm` (565): Constant terms of Weil functions along maps of positive degree
- `Lib/Weil/Periods/RealAndFinitePoints` (118): Real and finite points of the Bessel group
- `Lib/Weil/Periods/DescentVanishing` (653): Vanishing theta descents for unitary groups: Fourier coefficients and periods
- `Lib/Weil/Periods/Unfolding` (409): One step of the seesaw unfolding of the theta integral over the Bessel group

**Unramified**: Hecke operators at unramified places and theta lifts

- `Lib/Weil/Unramified/HeckeGL` (402): Hecke operators of GL_n at a finite place and local criteria for principal level
- `Lib/Weil/Unramified/SplitHecke` (315): Hecke operators and Hecke polynomials at split places; spherical eigenvectors
- `Lib/Weil/Unramified/HeckeTransfer` (478): Hecke polynomials pass through a theta lift
