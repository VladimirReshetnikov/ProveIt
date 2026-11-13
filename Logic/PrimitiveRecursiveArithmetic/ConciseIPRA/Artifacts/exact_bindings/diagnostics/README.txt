DIAGNOSTICS ARE NOT PROPOSED CHECKERS

reject_positional_mask_attack.json is the tiny false 0=S0 regression found
while developing the signed-mask alternative. The full discarded positional
prototype is explicitly labeled UNSOUND in verification/signed_mask/diagnostics.
It must not be used to check theorems. The final programs retain the original
three-positional-argument opener interface (a mask, where used, is keyword-only).

Actual-binding future-witness attacks are in
verification/actual_binding/fixtures/capture_*.json. They are rejected by the
corresponding final profiles. Their deliberately reordered negative controls
were tested independently; see the report and review notes.
