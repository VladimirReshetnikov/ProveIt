# Constructor descriptions in the frozen21-sign note

This corrects two register descriptions in Section1 of the frozen
`research/main-root-and-modulus-signs/README.md`, without changing its sealed
literal certificate, ordinary sign conclusions or any equation. Root checked
the actual original rows in
`candidates/projected-radius-mixed-bounds/source/raw_builder.json`.

The exact constructors, with zero-based original row numbers, are:

* Row29: `raw36=raw2+1=y+1`. Thus raw36>=1 from the independent prefix
  nonnegativity proof. The prose description `M0+2>=2` is incorrect.
* Rows47–50: `raw60=raw4+2`, `raw61=raw60+raw1`,
  `raw62=raw61+raw2`, `raw63=raw62+raw3`. Hence
  `raw63=t+x+y+M0+2>=3`, because `t=raw4=raw0+1>=1` and
  x,y,M0 are nonnegative.
* Rows51–73: `raw64=raw63^2`, then each next register is the preceding
  register squared, ending at `raw86`. There are exactly23 squarings, so
  `raw86=(t+x+y+M0+2)^(2^23)>=3`. It is not an iterated square of raw36.

Neither constructor has a fixed parity under the retained prefix guards.
Their required conclusion in the21-sign proof is simply that the actual
seed exponents are at least1. Both corrected constructors prove that
conclusion. The actual431-step positive-constructor certificate already
uses the original rows, not the mistaken prose aliases; its independent
literal checker is unchanged. Every selected power-call/exponent identity
and every final guard sign therefore remains valid.

The same corrections apply when reading downstream ordinary arguments
that cite this frozen note. All existing whole-row certificates, coefficient
polynomials and packet manifests remain preserved. Subsequent work must
use these literal descriptions and must not infer evenness merely because
raw86 is an iterated square. No new Lean or internal-ZFC theorem is claimed.
