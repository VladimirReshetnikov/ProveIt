# A shorter complete arithmetic specification

Lean work is paused. This investigation uses ordinary mathematics and
Python finite checks only.

The initialization tile was corrected after the original transition-only
review missed its state occurrence. All current pages include that
correction and pass full943-tile and457-mode conjugacy checks. See
[INITIALIZATION_CORRECTION.md](INITIALIZATION_CORRECTION.md); the former
displays are preserved as superseded history.

The original complete P69 page prints a 1294-digit seed. A state-renamed
version now prints **one 771-digit seed**, using the same fifteen positive
unknowns and the same six-factor equation. Both new TeX files are standalone:
every numeral and coefficient definition is present inline. They render to
one Letter page without overfull boxes, and text extraction recovers every
seed digit exactly.

| Display | Seed digits | Coefficient-recipe nonwhite characters | Entire-page nonwhite characters |
|---|---:|---:|---:|
| Original page | 1294 | 2861 | 3584 |
| BFS fixed-base decoder | 771 | 2543 | 3160 |
| BFS decoder, collected selector polynomial | 771 | **2518** | **3135** |

Character counts use the same `pdftotext -raw` extraction. The coefficient
recipe starts at “Fixed coefficients” and ends after the seed; it excludes
the shorter new title and proof-boundary note. Thus the actual constant
recipe improves by 343 characters, about 12.0%; the seed alone improves by
523 decimal digits, about 40.4%. TeX source length is not a printed-glyph
metric: the collected standalone source is 5881 ASCII bytes, compared with
the original source after inlining its separately stored seed display.

## Closed arithmetic decoder

The new literal `A` contains four packed nonnegative integers:

```
N = A mod 2^426,
T = floor(A/2^426) mod 2^1675,
M = floor(A/2^2101) mod 2^206,
E = floor(A/2^2307).
```

The 772 digits of these four separate numerals fit into 771 digits when packed
this way. Their widths are part of the displayed definition, not an oracle.

Write `D_b(X,j)=floor(X/b^j) mod b`. For `j=2q+r`, `0<=q<215`, `r=0,1`, define

```
nu_j = D_2(N,j),       sigma_j = sum_(k=0..j-1) nu_k,
m_q  = D_2(M,q),       tau_q   = sum_(k=0..q-1) m_k,
e_q  = D_12(E,tau_q),
F_q  = 14(1-m_q)+m_q*(e_q+floor(e_q/9)+floor(e_q/10)+2floor(e_q/11)),
u_j  = nu_j*(1+sigma_j)+(1-nu_j)*D_216(T,j-sigma_j),
v_(2q+r) = D_2(F_q,2r),   d_(2q+r) = D_2(F_q,2r+1).
```

The page's action label remains
`((1-d_j)(512+u_j),512+j,d_j(256+u_j),v_j)`.
All sums are finite sums of constant indices, including the empty sum.
There is no recursion, sort oracle, machine simulation, table lookup, or
external program in this definition. The one literal `A` is printed in full
in each new TeX/PDF and in the companion `SEED.txt`.

The compression uses two facts about this particular finite machine.
Breadth-first discovery, starting at state 0 and scanning read 0 before read 1,
visits all 215 active states. Its 214 first-discovery targets can therefore be
recovered as `1+sigma_j`; the other 216 targets are stored in base 216.
In 144 of 215 rows the write/move pair is the default
`(write0=0, right0=1, write1=1, right1=1)`, whose four-bit code is 14.
The 71 exceptional row codes lie in
`0,1,2,3,4,5,6,7,8,10,12,15`; their base 12 digit is expanded by
`e+floor(e/9)+floor(e/10)+2floor(e/11)`.

## State-renaming equivalence and whole coefficients

Let `pi` send an original state to its discovery number and fix the halt
state 215. The saved 216-entry certificate is a bijection with `pi(0)=0`.
Every one of the 430 transitions satisfies

```
delta'(pi(q),read) = (same write, same direction, pi(next)).
```

The native initializer is also renamed: the compact recipe uses
`(3,4,4,512+2u_0)` rather than the former hardcoded698. Here the first
decoded target is1. Separate horizontal and vertical color bijections
map all943 native tiles and all457 compact modes, including the start,
halt, forbidden and initialization rows. Transition conjugacy alone
would not justify this additional compiler premise.

For any tape and head position, mapping only the control state by `pi`
therefore commutes with one transition. Induction on the number of steps
gives equal tapes, equal head positions and corresponding states at every
time. Since the sole halting state is fixed, blank halting is equivalent,
with the same halting time. This is the ordinary mathematical equivalence;
the finite replay checks its full transition-conjugacy premise. It does not
pretend to be a Lean proof of the induction.

The new decoder recovers all 430 renamed transitions exactly. Reconstructing
the native modes, arithmetic ranks and coefficient sums from them gives
byte-for-byte equality with direct construction of the renamed machine's
whole tuple. The original `beta`, `MC` and `MF_source` are unchanged in all
161235 bytes. The new `K` has 434054 bits and 54257 bytes, with SHA256
`562494dbbe6e4651e55697f28596e801e341d50338bb902781c252912f3b2163`.
Its value changes; it must not be described as the original compact54 K.
The existing native bit-width caps remain the same.

State conjugacy transfers the machine's halting interpretation. Using the
resulting tuple in a consistency equation also needs the uniform native/Pell
encoding argument for that machine. Native calibration and its internal
object-ZFC formalization remain explicit outstanding obligations.

## Removing two coefficient definitions

The second page variant removes `delta_(i,j)` and `c_i` altogether. Because
the arithmetic ranks permute 0..456 and the two receiver ranks are 374 and 4,

```
sum_i c_i*x^r_i = O*G_457(x)+lambda*sum_i ell_i*x^r_i
                 -(255*2^9+2^27)*x^374-(255*2^18+2^27)*x^4.
```

This identity follows by collecting the common ordinary coefficient and the
two exceptional receiver corrections. All 457 coefficients and the complete
resulting K bytes were checked, both for the original state labels and for
the new labels. Thus this display simplification is also available without
changing any coefficient value of the original page.

## Artifacts and reproducibility

`candidates/one-page-compression/bfs-fixed216/` preserves the first new
display; `bfs-collected/` contains the shorter display. Each has a standalone
`equation.tex`, `equation.pdf`, the literal seed, decomposed seeds, the full
state permutation, and a finite replay receipt. The permutation JSON and
source files are proof/provenance artifacts; the printed definition does not
read them. The original one-page directory is untouched.

```
python3 tools/research_seed_compression54.py --render
python3 tools/research_seed_compression54.py --render --collected-phi \
  --output-dir candidates/one-page-compression/bfs-collected
```

Run these commands from this research directory. A `python3 -O` replay of
both variants also passes, producing identical seed, state permutation,
standalone TeX and PDF bytes. Guards use explicit exceptions rather than
removable assertions.

A same-label target/flag split needs 1145 separate payload digits and keeps
all original coefficients. A variable-radix target scheme needs 705 separate
digits but adds a finite product and a longer halt-symbol decoder. These are
comparison probes, not the recommended printed specification. The fixed 216
scheme gives the clearest checked improvement using the operations already
accepted for the page.
