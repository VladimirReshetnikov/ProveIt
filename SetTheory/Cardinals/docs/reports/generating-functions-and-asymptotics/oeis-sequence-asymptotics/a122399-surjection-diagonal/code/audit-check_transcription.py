#!/usr/bin/env python3
"""Check mathematical transcription from the audited Markdown into final TeX."""
import hashlib, json, re
from pathlib import Path
P=Path(__file__).resolve().parents[1]
md=(P/'proof.md').read_text();tex=(P/'a122399-report.tex').read_text()
def normalize(s):
    for x in [r'\begin{aligned}',r'\end{aligned}','&',r'\\',r'\Bigg',r'\left',r'\right',r'\qquad',r'\quad']:
        s=s.replace(x,'')
    return re.sub(r'\s+','',s)
a=re.findall(r'\\\[(.*?)\\\]',md,re.S)
b=re.findall(r'\\\[(.*?)\\\]',tex,re.S)
assert len(a)==len(b)==31
assert all(normalize(x)==normalize(y) for x,y in zip(a,b))
x=re.findall(r'\\\((.*?)\\\)',md,re.S)
y=re.findall(r'\\\((.*?)\\\)',tex,re.S)
it=iter(y)
assert all(any(normalize(v)==normalize(w) for w in it) for v in x)
result={
    'display_equations_identical_after_layout_normalization':len(a),
    'all_original_inline_math_preserved_in_order':len(x),
    'new_inline_math_count':len(y)-len(x),
    'normalizations':['whitespace','aligned environment','alignment tabs','line breaks','delimiter sizes','quad and qquad'],
    'proof_sha256':hashlib.sha256((P/'proof.md').read_bytes()).hexdigest(),
    'tex_sha256':hashlib.sha256((P/'a122399-report.tex').read_bytes()).hexdigest(),
    'pdf_sha256':hashlib.sha256((P/'a122399-report.pdf').read_bytes()).hexdigest(),
}
(P/'audit/transcription_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS:',result)
