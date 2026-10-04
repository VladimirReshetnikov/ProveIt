# Review of the U15 repeated-block input interface

**PASS within the stated source and arithmetic scope.** I read the entire
[report](u15_unary_block_interface.md) and helper, and independently checked
the primary initialization passages and the matrix calculations. The new
result is an effective universal input family `U_S W^x V_S`, with fixed
eight-bit block `W=01010111`. Its matrix is hyperbolic. The 12-operation
matrix assembly is conditional on correctly indexed Pell coordinates;
neither their index relation nor unbounded semigroup membership is paid.
The established universal polynomial bound remains 84.

## Primary simulation and input boundary

I read Neary and Woods's [author PDF](https://mural.maynoothuniversity.ie/id/eprint/12416/1/Woods_FourSmall_2009.pdf),
including Lemma 2.1's source-machine restrictions and clockwise encoding,
Lemma 2.2's symbol-preserving bi-tag steps, and Definition 3.1, equations
(3)–(4), Table 1 and the initial U15 configuration. I compared these with
the placed dependency audit named in the author note. This was a textual
primary-source check; I do not claim a new visual table transcription or
an executable simulation of the arbitrary-program compiler.

The normalized source machine can count a unary input of length x+4,
subtract four internally and run any selected semidecider. A separate
nonblank symbol represents visited blanks, meeting the source restriction
without changing the initial run. The clockwise and bi-tag constructions
preserve that run and add fixed state/boundary symbols. Alphabet numbering
can place the input letter first. Thus the bi-tag initial word is
`e_1 a_1^(x+4) a_right a_left`, and the published ordinary-symbol code
turns its variable part into `((01)^3 11)^x` after absorbing four copies
into the fixed prefix. The source's start state and scanned delimiter
agree with the semigroup head cut in the displayed full word.

At x>0 the bi-tag input has at least seven ordinary symbols, and active
steps do not reduce that count. The proof therefore uses valid simulated
configurations, not an unsupported extension to malformed short words.
Halting and the final undefined J1 transition are inherited from the
same primary simulation and directed-semigroup theorem as the parent.
The new input theorem is an effective mathematical construction, with no
claim to have implemented or materialized arbitrary compiled programs.

## Independent arithmetic checks

A fresh one-off exact integer calculation reconstructed the letter
matrices directly from
`E_j=[[1+4j,2],[-8j^2,1-4j]]`, then multiplied the eight letters of W.
It recovered the stated matrix, determinant one and trace -8942. Squaring
that matrix recovered the displayed B, a0 and D and checked
`D^2=(a0^2-1)I` independently of the author's helper.

The four conjugation identities imply for every i>=1
`Q Phi(A_i) Q^-1=-G^(8i-6)H`. The strictly positive determinant-one
matrices G,H make every nonempty ordinary-symbol concatenation hyperbolic:
its absolute trace is an integer at least three. This proves the general
claim; bounded enumeration alone would not do so. Optional zero padding
before the fixed delimiter does not supply variable input data.

I also independently evaluated all twelve assembly rows using formal
coefficient pairs for chi and psi and distinct signed fixed coefficients.
They give four entries of `chi*(LR)-psi*(LDR)`, at cost 8M+4A. The quadratic
identity proves the indexed matrix-power formula for every natural x.
The Pell norm by itself permits index one at every requested x, so the
singleton-language example correctly exposes the missing input coupling.
The exponential trace argument excludes an arithmetic straight-line
loader using only x and fixed constants; it makes no lower-bound claim
about representations with integer witnesses.

## Replays and frozen scope

The author helper reads the actual S193 alphabet codes as pinned data.
Its four constant identities, sixteen symbol images, 256 two-block
products and thirteen indexed Pell powers pass fresh installed normal
and optimized exact-receipt replay from `/`. No predecessor, archived
compiler or historical test suite was executed. No complete Diophantine
source or new universal arithmetic bound follows from these finite checks.

| File | SHA-256 |
| --- | --- |
| `u15_unary_block_interface.py` | `07c19ad5a37267fa31391186ad041297ab99e8bf2739905443658a04aa37440a` |
| `u15_unary_block_interface.json` | `a08e400d61ae5df0a25916f899d7e1e9e0225bc1d1d40052d4dc89ed435c30a0` |
| `u15_unary_block_interface.md` | `cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452` |

The author note identifies its primary PDF and frozen dependency hashes.
The replay command and the two remaining arithmetic obligations are
recorded there. Universality of the separate raw-ones affine slice remains
unproved; it is not implied by this repeated-block construction.
