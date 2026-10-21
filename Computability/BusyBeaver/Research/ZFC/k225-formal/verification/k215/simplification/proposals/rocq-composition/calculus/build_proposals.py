# Locally authored static source rewrite; does not execute received code.
from pathlib import Path
p=Path(__file__).parent
aliases='''abbrev memberForm := QuotientModel.memberForm

abbrev translate := QuotientModel.translate

abbrev RelSat (mem : V → V → Prop) (env : Nat → V) := QuotientModel.RelSat mem env

theorem sat_memberForm (mem : V → V → Prop) (env : Nat → V) (i j : Nat) :
    Sat mem env (memberForm i j) ↔ Member mem (env i) (env j) :=
  QuotientModel.sat_memberForm mem env i j

theorem sat_translate (mem : V → V → Prop) (phi : Form) (env : Nat → V) :
    Sat mem env (translate phi) ↔ RelSat mem env phi :=
  QuotientModel.sat_translate mem phi env

theorem equalityFree_translate (phi : Form) : EqualityFree (translate phi) :=
  QuotientModel.equalityFree_translate phi

'''
s=(p/'upstream/KQ1Model.lean').read_text()
a=s.index('theorem relSat_congr');b=s.index('def modelSetoid',a);s=s[:a]+s[b:]
# Shared proof identical except model interface.
q=(p/'QuotientModel.proposed.lean').read_text();a=q.index('/-- Satisfaction respects');b=q.index('theorem quotient_extensional',a)
new=q[a:b].replace('ModelsCPGIC mem','QHyp mem');i=s.index('theorem quotient_extensional');s=s[:i]+new+s[i:]
a=s.index('def memberForm');b=s.index('def modelSetoid',a);old=s[a:b];s=s[:a]+aliases+s[b:]
s=s.replace('import BusyBeaver.ZFC.KQHyp','import BusyBeaver.ZFC.KQHyp\nimport BusyBeaver.ZFC.QuotientModel',1)
(p/'KQ1Model.proposed.lean').write_text(s)
# The real generator must do this AFTER transform; otherwise it rewrites the aliases back.
g=(p/'upstream/generate_kq1.py').read_text()
needle='    if f == "Basic":'
patch='''    if f == "Model":
        # These definitions and proofs use no model hypothesis. Reuse, do not fork.
        # Run after transform, which would otherwise rewrite QuotientModel aliases.
        start = t.index("def memberForm ")
        end = t.index("def modelSetoid ", start)
        assert "theorem relSat_congr " not in t[start:end], "Apply the source theorem relocation first"
        t = t[:start] + MODEL_SYNTAX_ALIASES + t[end:]
        t = t.replace("import BusyBeaver.ZFC.KQHyp",
                      "import BusyBeaver.ZFC.KQHyp\\nimport BusyBeaver.ZFC.QuotientModel", 1)
'''
assert needle in g;g=g.replace(needle,patch+needle,1)
idx=g.index('for f in FORKS:');g=g[:idx]+'MODEL_SYNTAX_ALIASES = '+repr(aliases)+'\n\n'+g[idx:]
(p/'generate_kq1.proposed.py').write_text(g)
print('model-independent block:',len(old.splitlines()),'to',len(aliases.splitlines()))
