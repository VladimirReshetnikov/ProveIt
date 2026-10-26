# Decimal seed and distinct names: held stage A only

CODE ONLY, NOT RUN. There is no final equation.tex or PDF in this directory.
Author `/root/radix53_probe_full_static` prepared this bounded converter under
ROOT's formatting direction. This is author work, not an independent approval.
The maintained parity-clause2999 equation and all parent artifacts remain exact.

`seed_to_decimal.py` is deliberately only a seed converter. It extracts the
entire436-character base62 seed from the pinned parent TeX, not a retyped table,
and writes only decimal.txt and RECEIPT.json to a fresh fixed /tmp directory.
It never emits TeX, imports project code, decompresses ports, computes P66 or
changes a mathematical coefficient. The whole DAG, four compressed ports,
source manifest, ordinary proof and finite certificate are hash-only inputs.
All nine input files must match their complete pinned bytes before conversion.

The first route starts at0 and repeatedly replaces v by62v+digit. Induction
over the436 characters proves that the result is exactly the parent's printed
sum of digit times62 to the corresponding fixed power. The output is str(v),
a canonical decimal numeral; int(text,10) must recover v. The second route
repeatedly applies divmod(_,62) exactly436 times to that parsed decimal value.
The remainder characters must reproduce EVERY original character in reverse,
and the remaining quotient must be0. Uniqueness of Euclidean quotient/remainder
proves equality of the whole integers, not a residue or truncated fingerprint.
The seed starts nonzero; no leading-zero convention is silently changed.
The decimal text has at most872 digits because62^436<100^436=10^872.
No value, digit count, decimal numeral or output hash has been predicted here.

The ten prospective negatives use the SAME production gates: three malformed
decimal strings (empty, signed, leading-zero), two wrong decimal values (last
digit changed and last digit removed), four malformed seeds (short, long,
leading-zero, nonalphabet character), and one changed parent byte of unchanged
length. Each must raise its exact expected ValueError. Two positive routes are
the whole base62 evaluation and decimal/reverse-base62 round trip. These counts
describe UNEXECUTED code; no positive or negative result has been observed.
All gates are explicit exceptions and remain active under optimization.

Only after two full nonauthor exact-final statics and a distinct ROOT release
may the held commands run once. The generator's --write mode requires an absent
output tree and uses exclusive files; default mode only compares both complete
outputs. Normal and optimized verification must reproduce identical saved data.
First failure preserves every partial file/capture and stops dependent commands.
No retry, output deletion, source repair, TeX compilation or rendering is included.

After the exact decimal output is reviewed, ROOT can author the literal TeX.
The intended global scalar aliases are q_- -> b; M_C -> M; M_F -> N;
N_0 -> P; N_1 -> Q; N_a -> U; N_k -> W; N_t -> Z; N_s -> G.
The geometric G_m(x) becomes g(m,x), freeing G for its scalar factor.
The decoder's old N/T_0/E_0 become upright mask/targets/moves; its digit function
may be written digit(A,b,k). Genuine finite table/index families stay indexed.
These are scoped alpha-renamings, not extra unknowns: the fifteen positive
unknowns remain J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma.
The full front, table, decoder, native calibration and all four ports are retained.
Substituting the exact same integer A and expanding the scalar aliases yields
the IDENTICAL specialized P66 polynomial. The existing ordinary theorem and
15-variable/66-operation/degree157 facts transfer by equality, without a new
proof or arithmetic evaluation. No generated TeX or physical-page gain is claimed.

The future page must keep the existing9pt body and7.7pt seed/footer settings.
A decimal numeral may need more lines. Its complete literal source must be
reviewed before a separate typesetting release; fit/readability are still unknown.
This stage has no placeholder pretending to be a final numeral or final equation.
SOURCE_PINS and HOLD bind the exact source/runtime boundary. Only inert author
text/hash/member/Git reads and source writing occurred; no converter import,
AST/parser/compiler, mathematical helper, version check, application, Lean,
TeX/PDF/raster generation, protected edit or commit ran.
