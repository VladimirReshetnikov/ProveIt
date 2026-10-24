# A new current-page candidate: thirteen positive variables, degree51

[equation.pdf](equation.pdf) and the standalone [equation.tex](equation.tex) give the complete ordinary13-positive90-operation, degree51 equation with every fixed constant defined on one Letter page. The body uses9-point type. The full436-character seed and62-character alphabet are printed and extracted exactly. The printed positive unknown `j_*` is the literal circuit's `j`; all indices in the coefficient section are bound fixed indices. There are no other Diophantine unknowns.

This is a separate proposed current page. It preserves the preceding fifteen-variable page and its historical artifacts. Moving from15positive/69operations/degree155 to13positive/90operations/degree51 saves two unknowns and lowers degree, at the cost of21 operations. It also uses the larger compact44 coefficient tuple rather than compact54:295,388 raw coefficient bytes. No claim is made that every simplicity metric improves.

The mathematical reduction is the frozen [ordinary13 proof](../../research/ordinary-unit-products/ORDINARY13.md). The new task here is to provide a complete short specification of a **coherent compact44 tuple** for the same state-renamed machine used by the436-character decoder. No compact54 polynomial coefficient is used. The ordinary native/calculus calibration remains inherited; Lean and internal object-ZFC formalization remain open and formalization is paused.

## Exact equation and degree

[polynomial.json](polynomial.json) retains all90 live arithmetic gates and13 positive coordinates of the frozen ordinary13 source. Only its explicit coefficient binding is changed. `K0` in that JSON is K on the page, and MF is the already shifted `MF_source`. Its49 multiplications,24 additions and17 subtractions are counted with fixed integer leaves and sharing free. Intermediate page abbreviations are arithmetic registers, not quantified coordinates.

The renderer compares the complete displayed algebraic schedule with all90 actual gates over freely varying coefficient symbols, using exact shared terms modulo operand commutation. It performs no numerical identity inference. The printed factors are the ordinary strong factor `1+(I²-Q)` and the exact auxiliary factor, not the normalized strong norm of an earlier variant.

The attained degree51 follows from the frozen uniform coefficient `-32(3beta)^15` at `j^15 F eta^7 X^6 Y^13 f^4 i^2 u gamma alpha`, independent of the other three ports. Beta is the same positive compact44 beta. The free gate schedule and its degree upper bound are unchanged. This is a new native numeral binding of the same universal arithmetic polynomial, not an equality between its two specialized expanded polynomials.

## The full machine and tile conjugacy

The decoded430 actions are the breadth-first renaming pi of all original active states, with pi(0)=0 and pi(215)=215. Every action has the same read/write/move and renamed target. Mapping just a run's control state by pi therefore commutes with each step. Induction preserves blank halting, time, head position and tape content.

The943-tile language also carries an initialization action. In the original language it is `(3,436,4,head(93,0))`; the first original action is write1/right/state93. The correct renamed initialization is **`(3,436,4,head(u0,0))`**, with u0=pi(93)=1, giving `(3,436,4,4)`. This is explicitly printed on the page. Retaining literal93 after renaming would break the full language conjugacy; checking only430 machine transitions would not repair that.

For the complete typed color maps, set `head(q,b)=2(q+1)+b`. On vertical colors, send head(q,b) to head(pi(q),b), while bit colors0/1 and control colors434..438 stay fixed. On horizontal colors metadata0..5 stay fixed; send each old `right(q)=6+rank_R(q)` to `6+rank_pi(R)(pi(q))`, and each `left(q)=205+rank_L(q)` to `205+rank_pi(L)(pi(q))`. These are bijections of all439 vertical and250 horizontal labels. Applying them to all943 old tiles gives exactly all943 new tiles, including initialization. Start and Forbidden remain fixed. Their ranks stay0 and1; the initialization tile happens to retain rank458, but no argument assumes that coincidence.

Color renaming commutes with every local edge equality, every periodic or padded tiling, and its distinguished Start/Forbidden conditions. Consequently the old Wang943 blank-halting theorem transfers with the same spatial/temporal dimensions and padding freedom. This is an ordinary mathematical proof from the explicit finite color-bijection premise, not a claim that two raw K values are equal.

## Binding every printed coefficient formula

The independent constructor first reconstructs the original943 tiles and authenticates their complete literal hash and all four original compact44 port bytes. It then reconstructs the renamed943 tiles from the displayed seed and formula. The following page definitions are checked separately from the native bit-field loop:

1. All943 printed floor ranks equal the complete native selector order, with Start0 and Forbidden1. The packed comparison key has four10-bit fields, so the displayed floor is exactly a strict-order indicator.
2. The printed label is `v=w+2^8n+2^17e+2^25s+127*2^34`. Every edge label lies within its original8/9/8/9-bit capacity. Its seven occupied/anchor bits are the constant positions34..40.
3. The selector contribution `(1+2^51)G943-2^10 sum v(t)x^rank(t)` equals every coefficient `1+1024(2^41-v(t))`. All selector coefficients are nonnegative.
4. Every one of the11 triples in the printed copy/anchor set C expands to exactly the original38 copy positions and three anchor coefficients. The two zero-coefficient dummy positions remain in the low-mask support E. Its complete support has986 positions.
5. The four bare K shifts30,62,1100,2201, the two clause bands4393/5495, and `B*rho^42=rho^8849` match the native recipe exactly. Every exponent in Phi is at most3296, so the reciprocal expression for K has an exact integer value; the full value is checked, not rounded or truncated.
6. The page's low mask, high mask and padding are authenticated in full. MF explicitly includes B-1; it is not the unshifted native mask. The mask populations are `pc(MC)=590069-986` and `pc(MF_native)=986`, with the same modulo4/8 promises as before.

The new native finite carry threshold is

```
118788496120850159560 < rho=147573952589676412928.
```

All66,062 native basis identities, two-band separation, anchor intersection, circumference and padding ranges still hold. Thus the generic complement-encoding/rotation proof of compact44 applies without modifying its arithmetic source.

The actual-rank cofinal controller also survives. The base `B=2^590069`, prime581197, order and non-Wieferich certificates are unchanged. Its only DC-dependent unit bracket is `H0=1+B*DC+B²(DR+1)`. Its new residues are46 modulo67,4050 modulo8807, and31053 modulo581197, all nonzero. The factors `B²-1` remain units at those primes. Hence the same Boolean dummy-subset argument supplies cofinal canonical ranks and odd/square-scale witnesses. No assumption that state renaming automatically preserves a numerical controller residue is made.

Accordingly the same native interface and calibrated canonical family used by compact44's ordinary theorem exist for this **entire new tuple**. The adaptive carrier, early rank, ordinary strong norm and auxiliary-index arguments in the frozen ordinary13 proof depend on that interface and its unchanged mask bounds/population promises. They transfer in the same dependency order. The native and calculus theorems are inherited ordinary mathematics, not newly established by these finite tests.

Only K changes. Its592,884-bit raw SHA256 is `4364134a56b54cf132beeb9acd8e832be68f9083f4359ace4a588a1ea76a60f7`. Beta,MC,MF_source are byte-identical to the original compact44 values. All four complete compressed payloads are included, and all four are bound to the new recipe together.

## Reproduce

From the repository root:

```
python3 Computability/DiophantineConsistency/tools/verify_one_page_tuple44.py
python3 -O Computability/DiophantineConsistency/tools/verify_one_page_tuple44.py
python3 Computability/DiophantineConsistency/tools/render_ordinary13_page.py --render
python3 -O Computability/DiophantineConsistency/tools/render_ordinary13_page.py --render
```

Only this new candidate directory is written. No frozen H10 emitter, numeral array, original coefficient generator or Lean process is executed. The constant constructor uses finite integer arithmetic and independent original-byte comparisons. The page is self-contained and does not invoke that constructor at evaluation time.

`VERIFY.json`/`VERIFY_OPTIMIZED.json` record the whole-tuple and conjugacy checks. `PAGE_VERIFY.json`/`PAGE_VERIFY_OPTIMIZED.json` record the full90-gate identity, one-page Letter layout,9pt body, absence of overfull boxes, every436 seed and62 alphabet characters, and the distinct printed Greek glyphs. Normal and optimized renders give identical TeX/PDF bytes. The final PDF was visually inspected. Hashes, finite arithmetic tests and ordinary proof review do not establish consistency, complete a Lean proof or supply an internal object-language ZFC derivation.
