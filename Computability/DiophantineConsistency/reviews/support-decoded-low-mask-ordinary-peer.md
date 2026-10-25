# Independent ordinary review: support-decoded low mask

**PASS; no unresolved ordinary finding.** This review binds the immutable
two-payload packet `research/support-decoded-low-mask`, final manifest
`d8a95c4e86684275149bad676c4f2fa328978e1d55cd6018b12ec7d81705c129`.
README is `a4ac6da6ff30f5fbdfb4e311318f463b5ab68b88da753e03c438b95c6a4acd4e`;
SOURCE_PINS is `ace6f54278522c30dec4e879f42cac5e0135fbe92489b34668c010dc8f659cd5`.
Neither payload was edited. The companion JSON records exact metadata
authentication and the bounded inert checks.

I read the entire README, including its complete proposed constant body,
the whole pins/manifest, the retained indexed ordinary proof and the
current accepted printed/extracted constant body. I independently checked
all28 direct pins and the README pin, both complete closed parent
inventories (47 and38 payloads), all943 existing tile records, the small
control table, whole-body edits and all four existing payload identities.
Only text, JSON, hashes and existing compressed byte payloads were read.
No application, decoder, compiler, verifier, TeX or PDF utility was run;
no new tuple or coefficient file was generated.

## Coefficients, carries and exact support

All943 stored tiles have four nonnegative integer fields. Their actual
field maxima are(249,438,249,438), so the printed8/9/8/9-bit bounds hold.
The indexed ordinary proof also supplies the complete nonoverlapping
enumeration0..942 and its fixed Start0/Forbidden1 distinction. This
review retains that accepted seed/table correspondence; it does not
execute the decoder or regenerate the language.

The four low fields occupy exactly bits0..33. Therefore

    127*2^34 <= v(t) <= 2^41-1,
    1025 <= 1+2^51-2^10*v(t) <= 1+2^44 < 2^45 < rho.

The README's weaker lower bound1 is sufficient. In particular selector1
is nonzero; it is not interchangeable with a zero dummy. The actual
Forbidden tile at selector1 is(5,0,0,0), consistent with the same bound.

The eleven control triples contribute exactly41 distinct exponents:
983..992,1003..1011,1013..1031,1095,2195,3296. Their coefficient powers
are exactly2^10 through2^50, each once. No control exponent overlaps
0..942 or either dummy1063/1064. The four nonsingleton lengths8,9,8,9
plus seven singleton entries account for all41. Thus all coefficients
of the complete Phi polynomial are nonnegative and less than rho=2^67;
its nonzero support has984 positions and is exactly E minus those two
dummies. There are no base-rho carries in Phi(rho), so the digit function
returns each literal coefficient, including zero at both dummy slots.

For0<=d<rho, floor((d+rho-1)/rho) is precisely the indicator d!=0.
Consequently the proposed finite digit/floor sum U is the sum of rho^e
over the984 nonzero positions. It contains selector1 and excludes both
dummies. The complete old support correction is therefore

    sum_(e in E minus {1}) rho^e = U-rho+rho^1063+rho^1064.

Substituting into the old MC formula gives

    MC = beta+rho-U-3*rho^1063-rho^1064
       = beta+rho-(rho+3)*rho^1063-U.

This checks both the selector1 correction and the additional old
two-unit subtraction at1063. It is an exact integer identity, not a
heuristic comparison of sparse supports or a sampled digit test.

## Whole tuple, dependency order and retained semantics

The new expression depends on Phi and the universal digit function D_b.
The complete dependency order is universal arithmetic D_b and the fixed
seed ->430 actions ->943 indexed tiles ->Phi ->new MC. The use of the
same D_b symbol in seed decoding does not read MC or Phi and introduces
no cycle. Every new summation bound is fixed, and all floors/remainders
remain in definitions of constants rather than the fifteen unknowns.

The entire proposed body differs from the accepted body in exactly two
places: remove the complete Define/E/Then paragraph, and replace the MC
line by the proved identity. All other bytes match, including beta, K,
MF_source, Phi, the full control table,943-family table, alphabet, all436
seed characters, decoder and footer. The existing compressed payloads
are byte-identical between both accepted parents; their existing raw
payloads authenticate to the four stated hashes and total295388 bytes.
The new MC equals the accepted MC symbolically; no new tuple-generation
run is asserted or needed for this ordinary identity.

Hence every one of the four integers is unchanged together. The accepted
complete66-gate polynomial, positive domain, native/controller/Pell
calibration and ordinary refutation/Con(ZFC) equivalence are retained
without a new coefficient specialization or mixed-tuple transfer.
Internal-ZFC/Lean formalization is not established by this review.

## Full-text comparison and precise limits

I independently extracted the accepted whole constant/footer body and
compared it with the entire inert TeX block in the README. Applying only
the two specified literal edits reproduces every proposed byte. The
complete source sizes4099->3978 bytes and3813->3701 nonwhite source
characters match the declared hashes and counts.

The exact old extracted Define/E/Then/MC segment occurs once and has122
nonwhite characters. The fully charged Unicode replacement stream has49.
Replacing that one segment gives the stated whole-suffix proxy2553->2480
and whole-page proxy3025->2952. The73-character difference is an extraction
proxy using the inherited PDF text, not a newly rendered measurement.
The recipe proxy2343->2270 uses that same explicitly conditional delta.
The existing complete D_b definition, alphabet and seed remain charged.

No conclusion follows here about new page fit, line breaks, glyph order,
readability, fonts, actual PDF length or visual acceptance. The nested
digit/floor notation may trade readability for shorter text. Any future
page/tool change requires complete actual-TeX/whole-tuple checks, reviewed
new code, separate execution release, deterministic rendering and visual
review. The retained carry threshold lies strictly between2^66 and2^67,
so this identity supplies no smaller-radix argument. No maintained page,
source, common report, frozen coefficient packet or Lean file was changed.
