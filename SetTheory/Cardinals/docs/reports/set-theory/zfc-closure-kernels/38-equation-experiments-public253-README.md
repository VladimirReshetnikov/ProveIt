# Public253 guarded shortcut and state-deletion experiments

**Outcome:** a certified whole-tape 3-to-1 transition shortcut in the attributed
public 253-state ZFC machine; the count remains **253 working states**. The
complete bootstrap reaches the same endpoint in **312,895** steps instead of
312,975. No machine below 253 states is claimed.

Run the independent certificate checker:

```sh
python check_certificate.py
python test_certificate.py
```

The checker validates the literal source/output tables, a 3,530-pair radius-two
inductive invariant with 7,044 closure obligations, the local whole-tape
shortcut, and both complete bootstrap endpoints. Its finite-invariant proof
does not infer a future guard from bounded execution. `PROOF.md` contains the
mathematical argument and full attribution. The eight targeted tests verify
rejection of corrupted certificates and the necessity of the left-zero guard.

| File | Purpose |
| --- | --- |
| `source_zfc253.tm` | Byte-identical original public253 table, attributed to mira-emmy, Mira-Cult, Jeff, and Wade's framework |
| `zfc253_shortcut.tm` | New one-row variant; 253 working states, separate terminal253 |
| `invariant_radius2.json` | Finite inductive window invariant covering the unbounded blank run |
| `check_certificate.py` | Independent standard-library certificate checker |
| `regenerate.py` | Untrusted generator for candidate table and certificates |
| `bootstrap_endpoint.json` | Full list of all178 one-cell positions and canonical digest |
| `verification_result.json` | Recorded successful certificate result |
| `test_certificate.py` | Eight focused positive and corruption-rejection checks |
| `PROOF.md` | Provenance, exact edit, soundness proof, reproduction, scope |
| `searches/` | Reproducible finite negative searches in larger state-deletion families |

The source machine's pinned origin is
<https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/machine/zfc_253.tm>.
The present certificate is an ordinary executable arithmetic check with a
written proof, **not** a newly compiled Coq or Lean theorem. The existing source
Coq verification and the original253 reduction remain their authors' work.
