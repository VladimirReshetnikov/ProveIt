Standalone Lean support for the two-order-test label proposal
===========================================================

Files
-----
PowerOrbit.lean contains four theorems in namespace LabelReplacement.
lean_check.log records the exact command used and its successful compiler output.
No original ProveIt source file is imported or modified by this supplement.

Verified versions
-----------------
Lean: 4.35.0
Lean commit: eb6cafb7290e8bd5f2937522d8d804f58f02bafc
Mathlib commit: 56a005855ea17e0b0958f73ec801ae140b0a1679
ProveIt revision audited: 89d12dd40424f1217fd818d84877b3da52396a3b

Reproduction
------------
Use a Mathlib checkout at the exact commit above with Lean 4.35.0 available.
After obtaining that checkout's dependencies and compiled Mathlib cache, run
the following from the Mathlib checkout, replacing the absolute file path:

    LAKE_JOBS=1 lake env lean /absolute/path/to/Lean/PowerOrbit.lean

The Mathlib command `lake exe cache get` can populate its compiled cache.
The supplied verification returned exit status 0 with no warnings. Each of
the four final #print axioms commands reported only propext, Classical.choice,
and Quot.sound. No theorem depends on sorryAx.

Formalized assertions
---------------------
1. no_prime_power_kills: in any monoid, if Coprime 3 K and
       w^(3*K) = 1,  w^K != 1,  w^3 != 1,
   then w^(ell^u) != 1 for every prime ell and natural number u.

2. six_power_not_dvd: if ell is prime and 0 < j*t < 2^s, then
       6^s does not divide j*(ell^u*t).

3. six_power_add_not_dvd: the same conclusion with modulus 6^(s+c),
   for any natural number c. The proposed source interface uses c = 6.

4. power_orbit_injective: let G be a group, z in G, and q,a,K natural
   numbers. Assume q > 0, Coprime 3 K, and put A = q^(3^a). Assume
       z^(q^(3^(a+1))) = z,
       (z^(A-1))^(3*K) = 1,
       (z^(A-1))^K != 1,
       (z^(A-1))^3 != 1.
   For every prime ell and natural number u, the function
       i |-> (z^(ell^u))^(q^i)
   is injective on the natural indices i < 3^(a+1).
   The proof uses Mathlib's minimal-period API; it does not assume that G
   is commutative or that z is a primitive root.

Suggested finite-field application
----------------------------------
Let E = F_(q^r), r = 3^b with b >= 1, and let z be a selected nonzero
root. Apply the group lemma in G = E^times, representing z as a unit.
The Lean parameter a equals b-1; thus the lemma's r is 3^(a+1).
Put A = q^(r/3), N = q^r-1, and K = (A^2+A+1)/3.

The finite-field identities give z^(q^r) = z and z^N = 1. Arithmetic
under q = 1 modulo 9 gives Coprime 3 K and N = 3*K*(A-1).
The required exclusions on w = z^(A-1) are precisely the selected-root
conditions z^(N/3) != 1 and z^(3*(A-1)) != 1. Supply these statements
in the units group, apply power_orbit_injective, and coerce the result
back to E. Commuting powers identifies the displayed map with the
source's i |-> (z^(q^i))^(ell^u).

This application still requires finite-field bridge lemmas. The supplement
does not formalize the formula for K, its coprimality, the exact polynomial
count, the common-norm order theorem, scalar normalization, or the changed
projector and Galois interfaces. Those arguments are proved mathematically
in the accompanying report and remain integration work. A successful run
of this file is not a rebuild or verification of the full GRH project.
