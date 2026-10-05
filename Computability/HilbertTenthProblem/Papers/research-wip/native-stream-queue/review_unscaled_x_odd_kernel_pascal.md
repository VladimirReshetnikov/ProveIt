# Independent review of the odd-q unscaled-X kernel example

PASS for the stated canonical-kernel counterexample; no correction
requested. I read the entire frozen root note and both metadata/scalar
receipts. The example does not claim an actual compiler zero, and it
does not settle the direct-X83 candidate.

Reviewed pins:

| Artifact | SHA256 |
|---|---|
|`unscaled_x_odd_kernel_root.md`|`b715c35529cec34c9e6dd2c6e36d966edefc098a94fb9e283d51d4fc73704571`|
|`unscaled_x_odd_kernel_root.json`|`7df63fa16a005088fff7ca2f799627ce93acb8b075386befbef3d0f718bbec68`|
|`unscaled_x_odd_kernel_root_checks.json`|`996390ba1e35355d920662fbea4436d3ce9fb7ce581b3a63e8c39318108785c2`|
|`unscaled_x_odd_kernel_root_checks.py` (hash only)|`d12f20fec77c9b0b743b7ecc72b16394ca82f054d213e3ce0c4fef2ac8ebe02b`|

I independently reconstructed the binomial coefficients by a newly
written Pascal-triangle recurrence, keeping columns0 through611 of
row1222. By symmetry these are exactly the coefficients of the displayed
polynomial in descending order. Horner evaluation with X=2^1223 then
produces its exact numerator; a modular Horner check using the same fresh
coefficient row produces the residue modulo3^12. This computation did not
read, import or run root's helper and used no saved source array.

The fresh values agree with every scalar datum in the receipt:

    Y mod3^12 = 452709 = 23*3^9,
    v3(Y)=9, X mod27=14,
    bit_length(Y)=747253,
    bit_length(Y/27^3)=747238,
    SHA256(hex(Y))=
    c0b09b5f941fabe318153b830833c0b5a3e3ad95d3d13d83e08d77c9801c631a.

The modular inverse of2 is legitimate, and the integer numerator is even
because its central binomial coefficient and every positive-power term
are even. The note's displayed shorter recurrence uses
binom(1222,j), j=0,...,611, in precisely the Horner order just described.
Its exact divisions are valid integer binomial recurrences; modular
division requires the stated separation of the3-adic valuation.

The positive mathematical completion also checks. The first/main
converse at X=2^R and the actual half-binomial Y supplies both strict
ratio slacks and h>0 without needing q|X. The gamma recurrence has
G3=2A+2, so u=3 gives delta=4, positive rho and sigma and the exact input
norm; it is expressly a kernel input component rather than a fixed
compiler's ordinary-input loader. At m_aux=2cR, the binomial expansion
proves c^2 divides psi_A(m_aux); the canonical minus congruences at
R=3 modulo4 and gcd(c,f)=1 prove the displayed T quotient is integral.
All normalized auxiliary and scaled strong factors are consequently
the literal current ones. No full Pell tuple was numerically produced.

**Review remark 1 (the exact limit of the counterexample).** It refutes
the proposed kernel implication from X=2^R and q^3|Y to a dyadic q,
even with the displayed size/parity conditions and positive canonical
kernel components. It supplies neither the authentic repunit/outer
equations nor native masks or an ordinary input. Besides q=27 being
below the recipe's B>=32, R=1223 is below the stronger actual outer lower
bound (2q−1)(q^2−1). These are additional reasons not to promote this
kernel example to a false accepted input. The author's numbered failed
inference and explicit full-source boundary preserve this distinction.

The half-binomial and normalized-completion proofs used here were read
inertly during the accompanying direct-X/bootstrap work. The two pinned
dependency hashes in the root receipt agree with their repository bytes.
The new Pascal/Horner evidence is recorded in
`complete83_direct_X_boundary_pascal.json`. No author, frozen,
predecessor or supplied program was executed or imported, no saved array
was evaluated, and no repository or Git state was changed.
