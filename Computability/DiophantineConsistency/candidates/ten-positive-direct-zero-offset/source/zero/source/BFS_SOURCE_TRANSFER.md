# Alternate complete ten-positive equation on one page

`equation.pdf` and its standalone `equation.tex` specify the **entire**
equation in ten strictly positive integers, including every fixed numeral,
on one Letter page. The degree is **816** and the literal evaluator has
**123** live binary operations. The body is9-point type. All436 seed
characters, all62 alphabet characters, every tile family, rank, decoder
and constant formula are printed. Evaluation invokes no external table,
file, hash, machine program or algorithm oracle.

This is a separate proposed page. It does not replace any canonical page.
Relative to the current13-positive90-operation, degree51 page, it saves
three unknowns while increasing degree and operation count. Those are
different simplicity measures; no global minimum is claimed.

## Exact displayed polynomial

The only unknowns are

```
j_*,F,alpha,i,T,w,Y,n,eta,zeta > 0.
```

The printed j_* is the circuit input `j`. Every other symbol above the
fixed-constant section is a polynomial abbreviation, and every index in
the constant section is fixed/bound. Printed A is the source register
`Am1`, namely A'-1 in the parent proof; printed H is H', Delta is
Delta', M is Mtot, Z is Znum and S is fs. The capital Sigma norm
abbreviations are distinct from the decoder's lowercase sigma indices.

`polynomial.json` supplies all123 gates over the free four-port
signature beta,K0,MC,MF. Its gate schedule is unchanged from the frozen
`ten-positive-scaled-norm-shared` result. The renderer checks the complete
transcribed displayed algebraic schedule against the whole circuit using
exact shared terms modulo associativity/commutativity of addition and
multiplication. It uses no numerical test or expanded-polynomial hash
as an identity proof. `SOURCE_PINS.json` and both `PAGE_VERIFY` receipts
retain that full schedule and the alias map. The printed K is `K0`.

The local transport saving is preserved: the earlier scalar4A is reused
in `(4A)I`. The complete displayed norm is the same28-operation F16
schedule. All73 multiplications,30 additions and20 subtractions remain
live; every unknown and fixed port is used. The universal123-operation
identity,495-term norm,425-term centered weighted-degree certificate and
original ordinary proof are frozen in the parent candidate.

The degree816 leading form omega0^8 is independent of K0,MC,MF, and beta
is the same positive Mersenne value. Thus changing the native K binding
below cannot cancel that leading form. The degree upper bound and the
exact circuit over freely varying coefficients are unchanged.

## Verbatim closed coefficient recipe

Everything from "The four fixed integers" through the end of the TeX
template is copied **verbatim** from `one-page-ordinary13`, including its
436-character seed, ordered62-character alphabet, fixed finite sums,
integer quotient/remainder decoder,943-tile union, floor ranks, complete
Phi formula, mask formulas and the corrected initialization tile.
The renderer checks that exact source-body equality and the unchanged
seed bytes. Its seed slot is fully expanded in `equation.tex`.

The four complete compressed payloads are also copied verbatim from that
page's coherent **BFS-renamed compact44** tuple. They are included under
`coefficients/`. Their raw values are independently reconstructed from
the printed recipe in both normal and optimized Python; all four byte
comparisons pass. The page's reciprocal intermediate in K cancels
exactly. MF contains beta already and is not shifted a second time.

This tuple differs from the original compact44 tuple only in K. Its K
has592884 bits and raw SHA256
`4364134a56b54cf132beeb9acd8e832be68f9083f4359ace4a588a1ea76a60f7`.
Beta,MC,MF are byte-identical to their original compact44 values. No
compact54 numeral is used. In particular, **the old and new specialized
expanded polynomials are not claimed equal**. The universal arithmetic
recipe is equal; its new native numeral binding is justified below.

## Why package61's source interface transfers to this whole tuple

The state permutation pi is the complete breadth-first renaming of all215
active states, with pi(0)=0 and pi(215)=215. All430 decoded transitions
have unchanged read/write/direction and the renamed target. Mapping a
run's control state by pi commutes with every step and preserves the
blank tape, head position, time and halting. This is a full transition
isomorphism, not a test of a few runs.

The native language has additional initialization/control tiles. On its
439 vertical colors send head(q,b)=2(q+1)+b to head(pi(q),b), preserving
bit colors0/1 and control colors434..438. On its250 horizontal colors
preserve metadata0..5 and send each right/left state color to the
corresponding renamed target-rank color. Both maps are bijections, and
applying them to **all943 old tiles** yields exactly all943 new tiles.
Start `(2,435,3,1)` and Forbidden `(5,0,0,0)` are fixed.

Crucially, the original constructor tile
`(3,436,4,head(93,0))` becomes
`(3,436,4,head(u_0,0))=(3,436,4,4)`, because the first target93 is
renamed1. The printed tile union includes this actual decoded target.
Keeping literal93 would fail the conjugacy and would invalidate the
argument. The independent checker verifies the complete typed-color
map, including this tile.

Color bijections preserve every local edge equality and hence every
periodic/padded tiling with the same dimensions and distinguished
Start/Forbidden conditions. The Wang943 blank-halting interpretation
therefore transfers. Its compact native arithmetic proof also needs
numerical conditions, which cannot be inferred merely from graph
isomorphism. They are reconstructed and checked separately:

* All labels fit the original8/9/8/9-bit capacities. Every printed floor
  rank equals the complete native selector order. The old literal943-tile
  hash and original four compact44 numeral bytes are authenticated first.
* Every printed Phi/copy/anchor coefficient matches the native loop;
  all986 low-support positions, dummy positions, both clause bands,
  anchor intersection, circumference and padding ranges are preserved.
* All66062 native basis/convolution identities hold. The carry threshold
  is118788496120850159560, strictly below rho=147573952589676412928.
  Thus the uniform complement-encoding and rotation arguments apply.
* Beta and both masks are unchanged, with exactly the old bounds and
  populations: popcount(MC)=590069-986 and popcount(MF_native)=986;
  MC=2 modulo4 and MF_native=4 modulo8.
* The actual-rank cofinal controller needs its DC-dependent bracket
  `H0=1+B*DC+B^2(DR+1)` to be a unit at67,8807,581197. The new residues
  are46,4050,31053, all nonzero; B^2-1 is also a unit at each prime.
  B, the prime581197, the order and non-Wieferich certificates are
  unchanged. The same controller proof therefore supplies the same
  cofinal canonical ranks and odd/square-scale padding freedom.

Consequently the **uniform native interface and canonical family** used
to prove package61's normalized positive source theorem hold for this
entire new tuple. In particular its canonical q=B^N with odd N>1,
R=3 modulo4, X=2^R and ordinary Pell-coordinate promises survive.
The original K-specific source theorem is not applied by asserting that
K stayed numerically equal. Its parameterized native/compiler proof is
instantiated with the regenerated coefficients after checking all its
finite arithmetic/controller premises, then composed with the complete
state/color conjugacy and the original blank-machine/refutation theorem.

The scaled10 proof can now use that transferred source theorem exactly
where it used the original one. Its local soundness uses the same mask
bounds, odd beta and positive K. It reconstructs fresh unscaled source
witnesses, so it does not require the source's Pell witnesses to survive
the scaling. Completeness uses exactly the transferred canonical
promises. All these premises are present for the new tuple; none
requires the original state numbering or the original numerical K.
Thus the printed positive zero existence is equivalent, in the same
ordinary mathematical sense, to finite syntactic ZFC refutation.

`TUPLE_VERIFY.json` and `TUPLE_VERIFY_OPTIMIZED.json` retain the complete
state/typed-tile/native/controller receipts and the four whole raw-byte
comparisons. These finite checks establish the concrete premises of the
uniform argument. They do not replace its ordinary semantic proof.

## Layout and reproduction

The rendered Letter page has9-point body type, no overfull boxes, all436
seed characters and all62 alphabet characters extracted exactly, and
distinct Greek glyphs. Both standalone and template TeX sources are
included. The page was visually inspected at1600-pixel height: both
columns, the full norm schedule, corrected initializer, alphabet and
entire seed are legible, with no overlaps or clipping.

From the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/render_scaled10_page.py --render
python -B -O Computability/DiophantineConsistency/tools/render_scaled10_page.py --render
```

The independent closed tuple constructor is
`tools/verify_one_page_tuple44.py`; run it with a scratch `--output`
directory containing the copied `SEED.txt`, then compare the four raw
payloads with this candidate. It writes no frozen artifact. Normal and
optimized renders give identical TeX/PDF/polynomial bytes. The final
manifest omits ignored LaTeX scratch files; retained diagnostics use
ordinary `.txt` names so every sealed artifact can be tracked normally.

No canonical PDF, source candidate, old numeral payload or original
coefficient generator was changed. No proof assistant was run. Native
calibration and the internal object-ZFC derivation remain open in Lean;
formalization remains paused. This page is a complete finite equation
specification, not a proof that it has no solutions or a proof of ZFC
consistency.
