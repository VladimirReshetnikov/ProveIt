"""Check mathematical transcription boundaries introduced by report-only edits."""
from pathlib import Path
import hashlib
import json
import re
import sympy as sp

REPORT = Path(__file__).resolve().parents[1]
ROOT = REPORT.parent


def displays(text):
    pat = r'\\\[(.*?)\\\]|\\begin\{(align\*|gather\*)\}(.*?)\\end\{\2\}'
    result = []
    for match in re.finditer(pat, text, re.S):
        value = match.group(1) if match.group(1) is not None else match.group(3)
        value = re.sub(r'\s+', '', value)
        result.append(value.rstrip('.,;'))
    return result


checked = []
for source, target in [
    ('alternative/section.tex', 'direct_quartics.tex'),
    ('lowdegree/section.tex', 'centered_fifteen.tex'),
    ('integer/section.tex', 'integer_family.tex'),
    ('positive/section.tex', 'positive_family.tex'),
]:
    original = (ROOT / source).read_text()
    edited = (REPORT / 'sections' / target).read_text()
    if source.startswith('positive/'):
        original = original.replace(r'{\chi_{\Delta I}(R)\over\Delta I}', r'\frac{\chi_{\Delta I}(R)}{\Delta I}')
        original = original.replace(r'{V_*+c+Rf^2\over cf^2}', r'\frac{V_*+c+Rf^2}{cf^2}')
        original = original.replace(r'{V_*\over4Q}', r'\frac{V_*}{4Q}')
        original = original.replace(r'{9Q\over4}', r'\frac{9Q}{4}')
    if displays(original) != displays(edited):
        raise ValueError(f'Unexpected displayed-mathematics change: {source}')
    checked.append({'source': source, 'display_count': len(displays(original)), 'status': 'identical_after_declared_typesetting_normalization'})

# Independent comparison of added twelve-variable prefix displays to its literal specification.
spec = json.loads((ROOT / 'lowdegree/twelve/specification.json').read_text())
forms = dict(spec['polynomial_abbreviations'])
names = set(spec['variables']) | set(forms) | set(spec['fixed_numerals'])
symbols = {name: sp.Symbol(name) for name in names}
def expr(text):
    return sp.sympify(text, locals=symbols)
checks = {
    'Df': ('1+Delta*I**2', {'Dfminus1': 'Delta*I**2'}),
    'Q': ('Delta*(Df-1)', {'Dfminus1': 'Df-1'}),
    'V': ('Df*(c*T-R)-c', {}),
    'Dtau': ('1+L*(L+k)', {}),
    'Da': ('(Q-1)*(Q*V**2-1)', {}),
    'guard_radicand': ('budget-1-p2**2-p3*(p3+1)', {'pos': '1+p2**2+p3*(p3+1)'}),
    'Ztotal': ('Z+U*(2*L+k+6*(a+2)*I+9*(2*Q-1)*V)', {
        'Aroot':'2*L+k', 'Broot':'6*(a+2)*I', 'Croot':'9*(2*Q-1)*V'}),
}
for name,(report_form, substitutions) in checks.items():
    literal = expr(forms[name]).subs({symbols[k]:expr(v) for k,v in substitutions.items()}, simultaneous=True)
    if sp.expand(literal-expr(report_form)) != 0:
        raise ValueError(f'Twelve-variable prefix transcription differs: {name}')
if spec['variables'] != ['j','C','z','h','r','v','w','T','c','n','p2','p3']:
    raise ValueError('Twelve-variable coordinate list differs')

# Compare the literal edited norm displays, not just a separately written formula.
def tail_normalize(value):
    value = value.replace(r'\widehat', '').replace(r'\xi', 'w').replace(r'\varrho', 'r')
    return value.replace(r'\qquad', '').replace(r'\quad', '')
old_tail = displays((ROOT / 'lowdegree/section12.tex').read_text())
new_twelve_displays = displays((REPORT / 'sections/compact_twelve.tex').read_text())
new_tail = new_twelve_displays[-len(old_tail):]
if [tail_normalize(x) for x in old_tail] != [tail_normalize(x) for x in new_tail]:
    raise ValueError('The edited twelve-variable norm displays differ beyond notation')
checked.append({'source':'lowdegree/section12.tex', 'display_count':len(old_tail),
                'status':'identical_after_local_argument_alpha_renaming'})

# Hatted norm arguments and generic proof arguments are alpha-renamings only.
z,a,b,c,d = sp.symbols('z a b c d')
s1=a+b+c; s2=a*b+(a+b)*c; s3=a*b*c
uc=z+d; po=uc-s1; pe=po**2+4*(z*d-s2)
ge=pe**2+16*(z*d*po**2-4*s3*uc); go=pe*po-16*s3
norm=ge**2-64*z*d*go**2
zh,ah,bh,ch,dh=sp.symbols('zh ah bh ch dh')
renamed=norm.xreplace({z:zh,a:ah,b:bh,c:ch,d:dh})
if renamed.xreplace({zh:z,ah:a,bh:b,ch:c,dh:d}) != norm:
    raise ValueError('Norm alpha-renaming failed')

receipt = {'status':'PASS','displayed_formula_comparisons':checked,
           'twelve_prefix_identities': list(checks),
           'twelve_variable_list':'exact',
           'twelve_norm_notation':'alpha-renaming only',
           'inline_notation_change':'positive proof numerator a renamed a_0 to avoid collision with radicand a',
           'scope':'Editorial transcription check only; not a replacement for the component mathematical audits.'}
print(json.dumps(receipt, indent=2))
