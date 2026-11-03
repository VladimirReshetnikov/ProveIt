# Exact degree of the 74-row trace candidate

For the pinned direct-BFS fixed integer payloads, the candidate graph has
exact total degree **402** in its ten witnesses. This independent finite
check does not assume the parent degree. The graph and every raw and
compressed payload are hashed against its retained metadata.

At each gate the script propagates an upper bound for total degree. Addition
and subtraction use the maximum input bound and multiplication uses the sum;
the output bound is 402. Independently, substituting `t` for each of the ten
witnesses and reducing the four actual fixed integers modulo the prime
1,000,000,007 gives coefficient `217255545` at `t^402`. The script computes
this coefficient alongside the same gate bounds, retaining zero coefficients
if leading terms cancel. The nonzero coefficient proves that the original
fixed-integer polynomial has total degree at least 402. Together with the gate
bound, this proves exact degree 402. No expansion of the huge polynomial is
needed, and a nonzero coefficient in a finite field is a rigorous lower bound,
not a random-sampling inference.

Run `python3 -I -S -B check.py`; the captured result is `observation.txt`.
This is an external degree certificate, not a Lean theorem about JSON, a
positive-domain equivalence, a halting bridge, or an iPRA endpoint.
