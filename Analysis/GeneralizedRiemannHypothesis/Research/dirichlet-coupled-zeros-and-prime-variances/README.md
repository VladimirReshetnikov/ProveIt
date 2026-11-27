# Inverse problems for Dirichlet zeros and prime variances

Three research papers based on Vladimir Reshetnikov's ProveIt repository.
Start with the 12-page paper in `coupled_zeros/`. Each folder contains a
compiled PDF and its complete LaTeX source.

## Results

1. **Recovering Dirichlet characters and Hermitian couplings from positive zeros.**
   The graph encoded in a coupled Dirichlet determinant can be recovered even
   when its primitive character labels are unknown and mix parities. For
   distinct labels, its positive zeros determine every principal minor and
   hence every edge of a graph Laplacian with nonnegative weights. A competitor
   with at most the same number of vertices that has too little multiplicity
   at only o(T) distinct positive ordinates up to height T gives exactly the
   same data. The paper proves a stronger lower-limit version. Repeated labels
   determine sums of minors with prescribed numbers of slots of each label.
   The local separation theorem detects both directions of excess in every
   sufficiently high triple-logarithmic window. In windows of radius at least
   a constant times the square root of log log T it gives a sequence of
   alternating discrepancies of length proportional to the radius.
2. **Sampling prime variances and recovering squared zero multiplicities.**
   For a three-point difference, the logarithmic gaps between successive
   scales must tend to zero for universal recovery from sampling. Even
   occasional missed intervals of fixed logarithmic length admit
   counterexamples with only simple and double ordinates. A quantitative
   inverse theorem transfers a relative logarithmic saving with exponent
   delta in the all-scale variance to a saving with exponent delta/4 in
   the sharp squared-multiplicity count, for 0 < delta <= 1.
3. **The missing frequencies of five-point prime variances.** For five
   consecutive nodes, if the autocorrelation of the weights at lag three
   is nonzero, there are at most two invisible positive frequencies.
   An explicit quadratic and a phase compatibility condition classify them.
   Both frequencies occur for a dense, countable subset of a local
   two-parameter family. If the lag-three autocorrelation vanishes, there
   are either no invisible positive frequencies or infinitely many.

## Arithmetic input and scope

The first paper uses the repository's RH and Dirichlet GRH input to put
the coupled zeros on the real ordinate axis. The sampling and five-node
theorems for positive measures are unconditional. Their applications to
prime variances use the zeta explicit formula under RH. The sampling
counterexamples are model spectra. The variance remainder used to estimate
the count for the actual zeta zeros is an additional hypothesis.

The proofs were produced for this archive and compared with the merged
article, the ten reports placed in Research, the six ZIP files in
docs/incoming at the snapshot, and relevant primary literature. They are
human-readable proofs with two exact finite checks. Global priority has
not been established. The upstream Lean development was taken as the
article's input. We did not rebuild it or formalize these new theorems.

## Source snapshot

ProveIt commit `00cadb961bbe77c74e5d082c4948f8884d58a970`.

- [Project and provenance](https://github.com/VladimirReshetnikov/ProveIt/tree/00cadb961bbe77c74e5d082c4948f8884d58a970/Analysis/GeneralizedRiemannHypothesis)
- [Coupled determinants and prime variances](https://github.com/VladimirReshetnikov/ProveIt/blob/00cadb961bbe77c74e5d082c4948f8884d58a970/Analysis/GeneralizedRiemannHypothesis/Article/sections/zer.tex)
- [Local zero windows and Euler coefficients](https://github.com/VladimirReshetnikov/ProveIt/blob/00cadb961bbe77c74e5d082c4948f8884d58a970/Analysis/GeneralizedRiemannHypothesis/Article/sections/rec.tex)
- [Four-node inverse theorem and five-node question](https://github.com/VladimirReshetnikov/ProveIt/tree/00cadb961bbe77c74e5d082c4948f8884d58a970/Analysis/GeneralizedRiemannHypothesis/Research/grh-two-open-questions/zero-stencils)
- [Source of the Dirichlet GRH input](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207)

## Rebuild and verify

From each paper's own directory, run the corresponding command with a
standard TeX Live installation.

```sh
latexmk -pdf coupled_zeros.tex
latexmk -pdf stencil_inversion.tex
latexmk -pdf five_node_frequencies.tex
```

For the finite calculations, run the following from the root of the
extracted archive. Both checks need only the Python 3 standard library.

```sh
python3 coupled_zeros/verify_cycle.py
python3 five_node_filters/check_five_nodes.py
```

The first calculation checks all sixteen coefficients of the four-cycle
polynomial and gives certified lower bounds for the two prime-witness
constants. The second certifies the nonzero Jacobian for the five-node
attainment theorem by rational interval arithmetic.
