"""Regenerate the inherited profile plot with the manuscript's Q notation.

All curves and numerical quadrature remain the delivered plotting method.
The original report and figure are immutable; only the canonical copy changes.
"""
from pathlib import Path
import hashlib, json, sys, types

sys.dont_write_bytecode=True
B=Path(__file__).resolve().parents[1]
local=B/'verification/.scratch-plotdeps'
if local.is_dir():sys.path.insert(0,str(local))
source=B.parent/'reports/corpus-corrections/code/12-relation-spaces-verify_stieltjes_zeros.py'
text=source.read_text(encoding='utf-8')
assert text.count("label=r'$P_n(x)$'")==1
text=text.replace("label=r'$P_n(x)$'","label=r'$Q_n(x)$'")
m=types.ModuleType('canonical_zero_profile')
m.__file__=str(source)
exec(compile(text,str(source),'exec'),m.__dict__)
m.ROOT=B
(B/'figures').mkdir(exist_ok=True)
m.make_figures()
import matplotlib, numpy, scipy
record=dict(source='../'+source.relative_to(B.parent).as_posix(),
    source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    mathematical_change='None: label P_n changed to Q_n to match the canonical reciprocal-gamma Appell notation.',
    matplotlib=matplotlib.__version__,numpy=numpy.__version__,scipy=scipy.__version__,
    pdf_sha256=hashlib.sha256((B/'figures/stieltjes_profiles.pdf').read_bytes()).hexdigest(),
    scope='Floating-point visualization of already proved asymptotics; not a root or error certificate.')
(B/'verification/zero-profile-redraw.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,indent=2))
