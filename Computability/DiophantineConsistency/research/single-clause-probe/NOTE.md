# Recover the Boolean phase before decoding one clean clause

This isolated finite checkpoint replaces the two clauses of the complete
admissible942 model with one clause at2011. The physical support, all942
admissible selectors, all34 weighted labels, the Boolean dummy977 and
zero-weight Start marker1005 are unchanged. The key change is the order
of the soundness argument, not an assumption that occupation is known.

The Boolean marker test alone is available before any clause decoding:
its current contribution is forced selector0, hence one. Low fields
have zero carry, and every nonzero fractional binary phase produces only
even temporal digits. Thus the marker mask forces fractional phase zero.
Its temporal source is some physical position f, giving
`r=1005-f` with `0<=r<=1005`. This uses every physical position and no
one-hot or label premise. At the sole clause, every possible temporal
preimage is `2011-r>=1006`, above the largest physical position1005.
The clause is therefore clean in every cell. Only then does its count
lemma recover at most one tile and all labels. The existing Start south
tests finish the integral phase argument, including oldtile942/newtile941
at exceptional offset20.

The whole new kernel and masks use

```
DC = rho^18 + rho^1005 + rho^2011*Phi(1/rho)
DR = rho^9
K = DC + rho^(L+9)
MC = beta - rho^977 - G_942(rho) - Psi(rho,1).
```

First reflection is1026, above the marker and every copy test. Every
temporal/spatial copy and the marker remain exact. The clause predecessor
at2010 is the adjacent coefficient sum plus `x1005`, because the bare
marker times the physical marker occurs exactly there. This extra unit
is included in its reset bound. The last product field3016 has value
`c0*x1005`; every later field is raw zero. Native core population is62:
43 clause tests,17 color copies, one marker and one origin test. Padding
is19 full fields3017..3035 plus low23 bits at3036, hence916 bits and
978 total native tests.

The probe compares every complete tested-field convolution, all978 coarse
marker offsets before decoding, all934 later support-phase candidates,
the full Boolean convolution envelope, the whole masks and shifted-origin
rank controls. The maximum Boolean convolution is3829914518400942, now
at the sole clause. All carry29 and reset bounds pass. Safe dummy maximum
exponents are2988,986,977, with their exponent-plus-one margins checked.

The first tested length `L=3037` is prime and gives `d=142739`. Exact
base-two and B orders are23 modulo47 and3036 modulo3037; all prime factors
2,3,11,23 are checked. Spacing is3036. Auxiliary prime
`lambda=173053=57*3036+1` exceeds d, with lift quotient17573 and lift
residue3041060370. The complete new K gives `H=(37,1231,21346)` modulo
47,3037,lambda. Dense polynomial, direct admissible-tile and whole-integer
K calculations agree.

The four whole fixed integers total **71,425 raw bytes**,23,264 fewer
than94,689. No front-gate or degree change is claimed. A scoped negative
control checks center2010: its local clause contains an extra marker
unit, and coarse offset1005 permits a temporal marker contribution.
This rejects that particular clean-clause argument, not every conceivable
alternative proof or a complete Diophantine witness.

```
python research/single-clause-probe/probe.py --write
python research/single-clause-probe/probe.py
python -O research/single-clause-probe/probe.py
```

A separate full ordinary proof, independent review and page/port binding
are required before promotion. All accepted predecessors remain frozen.
