# Independent source review: root-switch witness extraction

The source's mathematical extraction is valid under its explicit signed root and norm premises. If P<=0, the root satisfies `z>=b*(ell+k)>0`; for natural ell>=0 and k>=2, `(ell+k)²>1+ell*(ell+k)`, contradicting the norm. Hence P>0, so `nonneg_iff` supplies a model-natural positive representative Pn. This does not require any representation or upper bound for K0 at this fact level.

The pinned signed-magnitude theorem represents z by either sign of a natural magnitude. The scaled quotient theorem supplies tau with the stated norm and `z=±b*tau`; the norm gives tau>ell. Either sign gives signed `b|z`, and the exact free-ring certificate `hz-hw` gives signed `b|P`. Only after P is represented as Pn does the pinned signed-to-natural reflection provide `Pn=b*t`; positivity of Pn and b makes t positive. These are the premises of the independently reviewed fact-level switch, which constructs a positive replacement while preserving the first-root square.

The source does not derive its signed norm/root premises from a graph zero, preserve the other residuals or establish the existential zero map. Compact ports, other positivity facts, parent bridge, provider ancestry and the iPRA endpoint remain separate. The authored receipt reproduces; source tactics, casts and axiom reports have not been elaborated by Lean.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue-root-switch-extraction-independent/check.py | cmp - reviews/ordinary13-residue-root-switch-extraction-independent/result.json
python3 -I -S -B research/ordinary13-residue-root-switch-extraction-draft/check.py | cmp - research/ordinary13-residue-root-switch-extraction-draft/receipt.json
```
