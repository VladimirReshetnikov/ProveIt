# Adaptive factor-three cancellation: author record

26 October 2026. Root authored and fully read the new main, checks and
complete private driver before execution. Both first Lean invocations pass
in3.639s/2.722s, empty main and four reports using only propext/Quot.sound.
This is the author record; independent review is separate.

For all signed q,Y,X,t, from q^3 dividing Y and q^5 dividing
(4Y(X+1)+3)t, derive q^4 dividing t. There is no positivity, nonzero-q,
restored-source, canonical-seed, rank or Pell assumption. A client yields
q^4 dividing v when t=qXY-v. This addresses unrestricted J, where 3 may
divide q and gcd(q,H)=1 would be false.

The proof uses a literal four-term geometric inverse modulo q^4. If 3
divides q, write q=3a and Y=q^3s. Then H=3B and
B=1+36a^3s(X+1)=1+q*12a^2s(X+1). Cancel the literal nonzero integer3,
then the geometric inverse cancels B. Otherwise q modulo3 is1 or2,
giving explicit Bezout coefficients for q and3. Multiplying H by the
coefficient of3 produces a unit residue modulo q, handled by the same
inverse. No gcd, primality, valuation or additional import is needed.

The focused check q=3,Y=27,X=1,t=81 proves all hypotheses while q^5 does
not divide t: losing one power really is necessary on this full generic
domain. Zero q, signed generic inputs and the exact index-difference
client are retained. No full thirteen-input equation-zero assertion or
new size/consistency/HA endpoint is made.

Main source cf7ebc1c3af93eb4ca800f309c411445dd267d0bf7d3bda437620be6cc702a67;
checks e27a02f724c48dedd5bb13abe61bf057db8b577cc5a240655a320c875fe1911c.
Objects bcb54d6683b952870f88545ea5a85bfcb67ef335f89f30f45044385c6b18c4a8
and507de2832668555d0d96ee070918cc53c18da68afdcfc056025eaca3a20e24bb.
[Replay](native-adaptive-factor-three-replay.json) SHA
edf7cc2818c62575a64d9b4e63e1a00a9fd787b1f6b41c248291e25798964c1b;
[eleven-file manifest](native-adaptive-factor-three-replay/FILES.json) SHA
90903431fe426656a26c4a4f3ba366e82393e77af285a51b7dd37b66a3b23955.

Only the two leaves are fresh over25 cached current-source custom modules,
22 explicit external names and66 external companions. All1523 inherited
and explicit input observations matched before and after. No Foundation
or prerequisite build occurred. Lean4.32 -M6000 -j1 -DElab.async=false used
private regular nonsymlink outputs and the512MiB reserve at
`/tmp/native-adaptive-factor-three-root-author-vdeezhwu/lib`.

Two metadata errors preceded compilation and are preserved: the original
prepare driver treated list-valued LEAN_PATH as a colon-delimited string,
and the immediately following compile command then stopped on its absent
marker. Both occurred before a compiler invocation. The corrected prepare
uses the actual list, reauthenticates the full inventory and creates a
new private overlay. Neither Lean source changed after its first build;
no failed Lean invocation occurred.
