# Ordinary ZF power containers in the exact C-row order

`NativeZFContainers254` proves two fixed ordinary Foundation ZF sentences. The
second has precisely the binder and connective order of the native container
row. It does not yet identify a numerical decoder instance with that sentence.

The bridge translates the repository's external `SetTheory.Form` into the
actual Foundation set language. At binder depth k, source indices below k map
to bound variables and indices k+j map to free j. The structural satisfaction
proof quantifies over arbitrary corresponding valuations, including both
quantifier cases. This translation concerns standard external formulas; it is
not a decoder for arbitrary internal formula codes.

Actual Foundation ZF model axioms supply Extensionality, Separation, Pairing,
Union, Infinity and functional Replacement. Replacement totalizes a functional
partial graph with y=x when no output exists, applies the actual total
Replacement axiom, and carves its image by actual Separation. This avoids
assuming Collection or Replacement implies Collection without additional set
axioms. Infinity obtains an actual empty witness and constructs successors by
Pairing and Union. Power Set and Regularity are extracted separately.

The checked native `ZFRank.containers` theorem then gives, for every a, a
transitive membership container v containing a and a represented power bound
inside v for each x in v. Its dependencies are the extracted ZFAxioms,
Regularity and Power Set. No object-level Choice or external WellFounded
premise is added. Ordinary semantic completeness yields the two fixed proofs.
The canonical row sentence simply reorders the same conjunctions and names its
bound variables distinctly; these names have the exact de Bruijn structure of
the source row's repeated-label shadowing.

The final 380-line source and focused audit passed Lean 4.32.0 in run3: fifteen
ordered axiom reports, fifteen callers, zero warnings, and only propext,
Classical.choice and Quot.sound. Source/audit times are 3.589845s/2.049723s.
The check reused exactly ten native rank project objects, the recorded direct
Foundation Basic.Axioms boundary, and four toolchain anchors. All 38 recorded
inputs, actual first providers and the fresh object were checked after the
build. The complete Foundation namespace cache is provided but its entire
transitive object graph is not independently rebuilt or attested. IOpen/Ring
objects discovered by the common environment helper are explicitly unused
import anchors. No Cantor project object or same-source object variance occurs
in this closure. No dependency build or download occurred.

Run1 failed on ordinary elaboration: a substituted-away successor variable,
two term-substitution evaluations, and the quotation parser's restriction
against duplicate bound names. The repairs retain the equality before
substitution, add explicit evaluation normalization, and alpha-rename the fixed
quotation. Run2 elaborated without diagnostics but failed to write its object
because the new output namespace directory was absent. Run3 adds only directory
creation to the guard. Both failures and their exact source/audit/guard bytes
are preserved; failed sorry warnings were never accepted as a proof object.
The earlier prepared label correction is preserved too: its copied source was
already the 377-line row-sentence version, whereas the true original 354-line
source is separately retained.

Portable replay, after placement, is:

```bash
python Logic/Interpretability/ZFCinPA/check_native_zf_containers254.py --output /tmp/native-zf-containers-replay
```

The runner accepts explicit repo, dependency root, core and boundary evidence,
core object cache, complete Foundation namespace cache, source/audit, compiler
and library paths. Its default core evidence is the maintained exact native169
integration record. Packaging performs override and relocated prepare-only
checks and rejects changed source bytes, an occupied output directory and
Python -O. These preparations query lean --version and perform zero proof
builds; original run3 remains the only successful proof run.

The remaining C client is a finite typed alpha/substitution bridge with the
actual two label gates. Distinct a,b reduce to the canonical fixed row;
coincident a=b requires a separate irreflexivity/vacuity argument. Numerical
zero aliases are handled by the separately checked circuit interpretation,
not by assuming syntactic decoder homomorphism. G additionally needs a genuine
all-internal Collection proof template and decoder freshness for its container
label, including the literal decoder-zero exception. Neither fixed ordinary
sentence proves those internal schema instances, the complete bundle,
accepted-proof translation, or a PA consistency comparison.
