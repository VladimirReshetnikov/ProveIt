# Degree-separated congruence-norm equation over ten integers

This component gives one explicit integer polynomial in ten unrestricted integer unknowns, of exact total degree 3,327,556, with a 519-operation division-free arithmetic circuit. Absence of integer zeros is equivalent in ZFC to Con(ZFC), by the mathematical composition proved in section.tex and the explicitly imported compiler and Sun results.

## Replay

Run `python3 reproduce.py`. It rebuilds the three generated circuit/source/metric artifacts byte-identically and executes the independent verifier both normally and with Python optimization. The checker imports no builder and checks all source isolation identities, local gate identities, actual payload bindings, exact degree, and supplementary signed-congruence/source tests.

The proof is section.tex (also report.pdf). INSTANCE.json is the active binding. generated/sun10.json gives the complete polynomial as a DAG; generated/source_records.json defines every fixed recipe using the four included binary coefficient payloads. The ten variable leaves are named f,g,h,k,l,w,x,y,z,m. The proof denotes the first four free coordinates t,g0,h0,k0, because f=2t+1 and g,h,k are computed registers in the imported bridge.

No positivity or divisibility side conditions occur in the final equation. Powers have fixed integer exponents and are compiled into multiplication gates. No proof-assistant verification of the composite endpoint or global minimality is claimed. Finite checks do not prove the imported unbounded compiler theorem or Sun's number-theoretic bridge.

The congruence-norm finalizer is inherited from the new incoming Congruence Norms release. This iteration's contribution is a smaller source/finalizer composition, with compatibility and constructive residue restrictions proved explicitly. See NOTICE.md and SOURCE_PINS.json.

Additional reduction: replace Tc by Tc−2, omit the leading N² term of X, and divide the fixed coefficient of Y by4. Bit1 of Sc is zero once b is a binary square and g=bg0, so the removed mask bit was redundant. This preserves unconditional congruences needed by the finalizer and saves one gate. The complete proof is in section.tex.
