# Attribution and scope

This AI-assisted research contribution was prepared for Vladimir Reshetnikov's
ProveIt project on 24 October 2026. Its comparison snapshot is commit
45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6.

The new construction composes the incoming Coprime Projection and Powered
Saturation / Factorial Carriers Round14 proposals. Their exact archives are
identified by repository paths and SHA-256 values in SOURCE_PINS.json.
The ordinary proof dependencies and existing license and attribution texts
are retained under source/ and licenses/.

The DAG primitive in circuit.py and sparse polynomial primitive in
exact_polynomial.py are credited adaptations or copies from the Coprime
Projection integer component. build.py uses its unchanged native arithmetic
front end and changes only the stages proved in PROOF.md. check.py reuses
the source's exact free-ring-cut audit technique and independently transcribes
the complete selected new polynomial, degree proof, and all coefficient checks.

No historical-priority claim is made for Pell equations, squareclass
separation, intersective polynomials, CRT, or the general norm identity.
The new claim is the specified composition and the exact verified endpoint,
with the mathematical and formalization boundaries stated in PROOF.md.
