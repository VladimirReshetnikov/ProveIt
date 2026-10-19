COMPLETE E713 EQUATIONAL FRONTEND

This is a separate frontend research contribution. It does not implement
the 238-state machine and does not infer any binary-state count from bits.

Build and check all four complete packets:
  python3 build_packet.py

The final packet is generated/E713.bits (713 bit characters plus newline).
generated/E713.equations lists all eight fully expanded equations.
generated/E713.json gives all arities, endpoints, syntax and accounting.
kernel_note.tex is standalone; kernel_section.tex can be included in the
main report. The latter states the exact inherited raw-EPSC dependencies,
proves the complemented-witness binder and closure factoring, and supplies
both ordinary model directions and the ground-congruence calibration.

Quantifier warning: E713's Q means exists-not. It is not the ordinary
existential constructor of the old packet. The explicit translations are
Q_old(a)=Q(P(a,a)), W_old(s,a)=W(s,P(a,a)), Pick_old(x)=W(x,d).

Every emitted packet includes its signature, all equations and two ground
endpoints. Arithmetic count: 52 header bits + 645 equation bits + 16 endpoint
bits = 713. Its eight equation-node counts are 14,6,6,10,12,12,17,82.
Predicate values are mapped through an ultrafilter before the lower
interpretation uses two-valued branch logic; native objects are not quotiented.

The inspected946 packet is reconstructed byte-for-byte by build_packet.py.
The measured saving is233 bits (24.63 percent); the quantifier transformation
alone saves29 bits. We do not claim global optimality or exhaustive priority.
Memory mentions an E766 packet, but that archive was unavailable for a
literal comparison. The quantitative baseline is the exact inspected946.

No Lean/Rocq endpoint, internal PA proof, or finite test of consistency is
asserted. See generated/verification.json and independent review files for
the exact finite algebra and serialization validation scope.
