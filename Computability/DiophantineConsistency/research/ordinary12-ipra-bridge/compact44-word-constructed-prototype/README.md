# Constructed compact word from definable cells

`CompactConstructedWord.lean` defines a word as the represented block sum
of the uniformly normalized compact cells. For Σ₁-definable model functions
`row` and `dummy`, and any model length `N`, it proves the word is bounded by
`2^((67*8807)*N)`. At every `j<N` and subposition `p<8807`, its radix-`2^67`
digit agrees with `cellDigit (row j) (dummy j % 2) p` and is at most one.
The clients specialize this to all 943 selector positions, all 41 payload
copy positions and the dummy position, whose digit is `dummy j % 2`.

This constructs the packed number for arbitrary definable row and dummy
functions, including nonstandard model lengths. It does not show that a
particular row function encodes a valid computation, that the first row is
zero, that any full low- or high-mask/product condition holds, or that the
compact equation has a graph zero. It is not an object-theory iPRA proof.

The first two guarded attempts failed on instance synthesis and then on an
unfolded expression mismatch; their exact sources and logs are retained. The
third exited 0 with unchanged sampled direct dependency/companion guards, no
warnings or `sorryAx`, and only `propext`, `Classical.choice` and `Quot.sound`
in the six named axiom reports. All three attempts are single-author, with
provider, package, transitive, dynamic-loading and between-observation
ancestry inherited. The runner's `/tmp` providers may be ephemeral.
