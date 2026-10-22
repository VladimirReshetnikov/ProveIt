"""Re-run the repository's bisimulation-quotient modules on the `KQHyp.QHyp` interface.

  python generate_kq1.py      (from Computability/BusyBeaver/Lean)

Forks QuotientModel, QuotientSeparation, QuotientBasic, QuotientReplacement, QuotientPower and the
collection part of QuotientCPGIC into KQ1Model ... KQ1Collect. The hypothesis `h : ModelsCPGIC mem`
becomes `h : QHyp mem`; the four `eqv_*_of_model` laws, the profile pairs and the GIC half `h.2`
become fields of `h`; the three results that read the CP containers (interpreted union, power and
singleton-closed containers) become the fields `h.union`, `h.power`, `h.singleton`. The proofs
are otherwise the originals.
"""
import re
from pathlib import Path

D = Path("BusyBeaver/ZFC")
FORKS = ["Model", "Separation", "Basic", "Replacement", "Power"]

COMMON = [
    ("import BusyBeaver.ZFC.CompositionModel", "import BusyBeaver.ZFC.KQHyp"),
    ("(h : ModelsCPGIC mem)", "(h : QHyp mem)"),
    ("(h : ProfileModel.ModelsCPGIC mem)", "(h : QHyp mem)"),
    ("(h : ProfileModel.ModelsCPGIC rawMem)", "(h : QHyp rawMem)"),
    ("eqv_refl_of_model mem witness h", "h.refl"),
    ("eqv_symm_of_model mem witness h", "h.symm"),
    ("eqv_trans_of_model mem witness h", "h.trans"),
    ("eqv_extensionality_of_model mem witness h", "h.ext"),
    ("pairs_of_model mem witness h", "h.pairs"),
    ("h.2", "h.gic"),
]


def transform(text):
    for a, b in COMMON:
        text = text.replace(a, b)
    text = re.sub(r"import BusyBeaver\.ZFC\.Quotient(\w+)", r"import BusyBeaver.ZFC.KQ1\1", text)
    text = re.sub(r"ZFC\.Quotient(Model|Separation|Basic|Replacement|Power|CPGIC)\b", r"ZFC.KQ1\1", text)
    text = re.sub(r"\bQuotient(Model|Separation|Basic|Replacement|Power)\.", r"KQ1\1.", text)
    # the interface namespace
    text = re.sub(r"^(namespace SetTheory\.BusyBeaver\.ZFC\.KQ1\w+)\n", r"\1\n\nopen KQHyp\n", text,
                  count=1, flags=re.M)
    return text


def replace_theorem(text, name, new):
    i = text.index(f"theorem {name} ")
    m = re.search(r"\n\n(?=(theorem |def |#print|/--|end |noncomputable ))", text[i:])
    return text[:i] + new.rstrip() + "\n" + text[i + m.start():]


HEAD = ("/- Forked by Research/ZFC/k225-formal/generate_kq1.py from {src}.lean onto the "
        "KQHyp.QHyp interface; do not edit. -/\n")

MODEL_SYNTAX_ALIASES = 'abbrev memberForm := QuotientModel.memberForm\n\nabbrev translate := QuotientModel.translate\n\nabbrev RelSat (mem : V → V → Prop) (env : Nat → V) := QuotientModel.RelSat mem env\n\ntheorem sat_memberForm (mem : V → V → Prop) (env : Nat → V) (i j : Nat) :\n    Sat mem env (memberForm i j) ↔ Member mem (env i) (env j) :=\n  QuotientModel.sat_memberForm mem env i j\n\ntheorem sat_translate (mem : V → V → Prop) (phi : Form) (env : Nat → V) :\n    Sat mem env (translate phi) ↔ RelSat mem env phi :=\n  QuotientModel.sat_translate mem phi env\n\ntheorem equalityFree_translate (phi : Form) : EqualityFree (translate phi) :=\n  QuotientModel.equalityFree_translate phi\n\n'

for f in FORKS:
    t = (D / f"Quotient{f}.lean").read_text(encoding="utf-8")
    t = transform(t)
    if f == "Model":
        # These definitions and proofs use no model hypothesis. Reuse, do not fork.
        # Run after transform, which would otherwise rewrite QuotientModel aliases.
        start = t.index("def memberForm ")
        end = t.index("def modelSetoid ", start)
        assert "theorem relSat_congr " not in t[start:end], "Apply the source theorem relocation first"
        t = t[:start] + MODEL_SYNTAX_ALIASES + t[end:]
        t = t.replace("import BusyBeaver.ZFC.KQHyp",
                      "import BusyBeaver.ZFC.KQHyp\nimport BusyBeaver.ZFC.QuotientModel", 1)
    if f == "Basic":
        t = replace_theorem(t, "interpreted_union", """theorem interpreted_union (mem : V → V → Prop) (witness : V)
    (h : QHyp mem) (a : V) :
    ∃ b, ∀ z, Member mem z b ↔ ∃ x, Member mem x a ∧ Member mem z x :=
  h.union a""")
        t = replace_theorem(t, "interpreted_singleton_closed", """theorem interpreted_singleton_closed (mem : V → V → Prop) (witness : V)
    (h : QHyp mem) (root : V) :
    ∃ v, Member mem root v ∧ ∀ x, Member mem x v →
      ∃ s, Member mem s v ∧ ∀ z, Member mem z s ↔ Eqv mem z x :=
  h.singleton root""")
    if f == "Power":
        t = replace_theorem(t, "interpreted_power", """theorem interpreted_power (mem : V → V → Prop) (witness : V)
    (h : QHyp mem) (a : V) :
    ∃ p, ∀ x, Member mem x p ↔ InterpretedSub mem x a :=
  h.power a""")
    assert "Containers" not in t and "h.1" not in t and "ModelsCPGIC" not in t, (f, [
        l for l in t.splitlines() if "Containers" in l or "h.1" in l or "ModelsCPGIC" in l])
    (D / f"KQ1{f}.lean").write_text(HEAD.format(src="Quotient" + f) + t, encoding="utf-8", newline="\n")
    print("wrote", f"KQ1{f}.lean")

# the collection half of QuotientCPGIC
t = (D / "QuotientCPGIC.lean").read_text(encoding="utf-8")
i = t.index("/-- Matrix satisfaction respects both bisimulation-equivalent inputs. -/")
j = t.index("/-- Actual CP plus every native-Form GIC instance")
body = transform(t[i:j])
assert "Containers" not in body and "h.1" not in body and "ModelsCPGIC" not in body
hdr = t[:t.index("namespace SetTheory")]
hdr = transform(hdr).replace("import BusyBeaver.ZFC.KQ1Power", "import BusyBeaver.ZFC.KQ1Power")
out = (HEAD.format(src="QuotientCPGIC (collection part)") + hdr.split("/-!")[0] +
       "/-! Every Form has collection in the quotient (the GIC half of `QuotientCPGIC`). -/\n\n"
       "namespace SetTheory.BusyBeaver.ZFC.KQ1Collect\n\nopen KQHyp\n"
       "open Form Profile ProfileCollection ProfileComposition ProfileAxioms\n"
       "open ProfileSyntax ProfileModel CompositionModel DeepPositiveClosure\n\n"
       "universe u\nvariable {V : Type u}\n\n" + body + "end SetTheory.BusyBeaver.ZFC.KQ1Collect\n")
(D / "KQ1Collect.lean").write_text(out, encoding="utf-8", newline="\n")
print("wrote KQ1Collect.lean")

