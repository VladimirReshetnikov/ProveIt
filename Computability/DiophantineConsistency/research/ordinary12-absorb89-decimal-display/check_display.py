#!/usr/bin/env python3
"""Externally check both TeX and extracted PDF of the 12-variable draft."""
import argparse
from hashlib import sha256
import gzip
import json
from pathlib import Path
import re
import subprocess
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
DC = HERE.parents[1]
ROOT = DC.parents[1]
GRAPH = DC/'research/ordinary12-absorb89-probe/graph-dag.json'
ROWS = DC/'research/ordinary12-ipra-bridge/compact44-943-table-prototype/Compact943Data.lean'
SLOTS = DC/'research/ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean'
PAYLOAD = DC/'candidates/free-j-polarized-positive/source/positive/coefficients/payloads'
count = 89
A, B = HERE/'build01', HERE/'build02'

def need(condition, message):
    if not condition: raise RuntimeError(message)


def digest(data): return sha256(data).hexdigest()


original = {p: p.read_bytes() for p in (DC/'equation.tex', DC/'equation.pdf')}
graph_bytes = GRAPH.read_bytes(); rows_bytes = ROWS.read_bytes(); slots_bytes = SLOTS.read_bytes()
expected_graph_hash = '280b23e5be95692b9db0183affce4247d974320ded1e709f41b05cc7e32b2fdd'
need(digest(graph_bytes) == expected_graph_hash and
     digest(rows_bytes) == '10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8' and
     digest(slots_bytes) == 'f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae',
     'graph or symbolic table source pin drift')
for f in ('equation.tex','equation.pdf'):
    canonical = HERE/f
    need((A/f).read_bytes() == (B/f).read_bytes() == canonical.read_bytes(),
         ('repeated or published draft build mismatch', f))
tex_bytes = (A/'equation.tex').read_bytes(); pdf_bytes = (A/'equation.pdf').read_bytes()
tex = tex_bytes.decode(); graph = json.loads(graph_bytes)
need(graph['domain'] == 'strictly positive integers' and len(graph['source']) == count and
     graph['operations'] == count and graph['output'] == 'P12', 'graph metadata mismatch')
need('a,b,c,d,e,f,g,h,i,j,k,\\ell\\in\\mathbb Z_{>0}' in tex and
     (r'\boxed{\mathtt{r%02d}=0}' % count) in tex, 'unknowns or equation mismatch')
need('using ordinary integer\narithmetic; subtraction is integer subtraction, and intermediate values may be\nnegative.' in tex,
     'integer arithmetic clarification missing from TeX')
need('Overfull \\hbox' not in (A/'pdflatex.stdout').read_text() and
     'Overfull \\hbox' not in (B/'pdflatex.stdout').read_text(), 'overfull TeX box')

tokens = dict(zip(graph['witnesses'], list('abcdefghijk') + ['ℓ']))
tokens.update({'beta':'β', 'K0':'κ', 'MC':'μ', 'MF':'ν'})
pdf_expected = {}
for number, (name, op, x, y) in enumerate(graph['source'], 1):
    def operand(value):
        if type(value) is int: return str(value)
        need(value in tokens, ('invalid reference', number, value)); return tokens[value]
    pdf_expected[f'r{number:02d}'] = (operand(x), op, operand(y))
    need(name not in tokens, ('duplicate graph name', name))
    tokens[name] = f'r{number:02d}'
need(tokens[graph['output']] == f'r{count:02d}', 'output mapping mismatch')

extract = subprocess.run(['pdftotext', '-layout', str(A/'equation.pdf'), '-'],
                         capture_output=True, text=True, timeout=60)
need(extract.returncode == 0 and not extract.stderr, 'PDF text extraction failed')
page_one = extract.stdout.split('\f', 1)[0].replace('µ','μ')
need('using ordinary integer arithmetic; subtraction is integer subtraction, and intermediate values may be negative.'
     in ' '.join(page_one.split()), 'integer arithmetic clarification missing from PDF')
pattern = r'\b(r\d{2})\s*=\s*(r\d{2}|[a-kℓβκμν]|\d+)\s*([+−·])\s*(r\d{2}|[a-kℓβκμν]|\d+)'
matches = re.findall(pattern, page_one)
need(len(matches) == count and len({m[0] for m in matches}) == count, ('PDF graph coverage', len(matches)))
operations = {'+':'+', '−':'-', '·':'*'}
pdf_observed = {name:(x,operations[op],y) for name,x,op,y in matches}
need(pdf_observed == pdf_expected, 'PDF graph differs from pinned graph')

# Check mathematical formula tokens in the rendered TeX, independently of
# generator execution, then evaluate those formulas using the displayed data.
clean = re.sub(r'\s+', '', tex).replace('\\\\','').replace('&','').replace('\\quad','')
need(r'\rho=2^{67}' in clean and r'\beta=\rho^{8807}-1' in clean, 'radix/beta transcription')
expected_support = (r'\mathcalS={}\bigl(\{0,\ldots,942\}\cup\{983,\ldots,992\}\cup'
    r'\{1003,\ldots,1011\}\cup\{1013,\ldots,1031\}\cup'
    r'\{1063,1064,1095,2195,3296\}\bigr)\setminus\{1\}')
expected_mc = r'\mu={}\beta-\sum_{u\in\mathcalS}\rho^u-2\rho^{1063}'
expected_mf = (r'\nu={}\beta+4+\sum_{u=1013}^{1022}\rho^u+\sum_{u=1065}^{1073}\rho^u'
    r'+\rho^{2195}+\rho^{3296}+(2^{51}-2)(\rho^{4393}+\rho^{5495})'
    r'+(2^{65}-1)\sum_{u=8792}^{8804}\rho^u+(2^{19}-1)\rho^{8805}')
expected_k = (r'\kappa={}\rho^{30}+\rho^{62}+\rho^{1100}+\rho^{2201}+\rho^{8849}'
    r'+\sum_{u=0}^{942}\sigma_u(\rho^{4393-u}+\rho^{5495-u})'
    r'+\sum_{u=0}^{40}2^{10+u}(\rho^{4393-\lambda_u}+\rho^{5495-\lambda_u})')
need(all(x in clean for x in (expected_support,expected_mc,expected_mf,expected_k)),
     'constant formula transcription mismatch')
match = re.search(r'\\lambda=\{\}&\((.*?)\)\.',tex,re.S)
need(match is not None, 'slot-list not found')
printed_slots = [int(x) for x in re.findall(r'\d+',match.group(1))]
slot_source = slots_bytes.decode().split('def slots : List ℕ := [',1)[1].split(']',1)[0]
need(printed_slots == [int(x.strip()) for x in slot_source.split(',')] and len(printed_slots) == 41,
     'slot list mismatch')
table = tex.split('% BEGIN SELECTORS',1)[1].split('% END SELECTORS',1)[0]
printed = [int(x) for x in re.findall(r'(?<!\d)\d{14}(?!\d)', table)]
row_text = rows_bytes.decode().split('-- BEGIN PINNED ORDERED ROWS',1)[1].split('-- END PINNED ORDERED ROWS',1)[0]
rows = [tuple(map(int,x)) for x in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',row_text)]
expected = [1+1024*(2**41-(w+256*n+2**17*p+2**25*s+127*2**34)) for w,n,p,s in rows]
need(len(printed) == len(expected) == 943 and printed == expected, 'decimal selector table mismatch')
pdf_table = extract.stdout.split('Decimal selector list.',1)[1]
pdf_printed = [int(x) for x in re.findall(r'(?<!\d)\d{14}(?!\d)',pdf_table)]
need(pdf_printed == expected, 'extracted PDF selector table mismatch')

rho = 2**67; beta = rho**8807-1
support = (set(range(943)) | set(range(983,993)) | set(range(1003,1012)) |
           set(range(1013,1032)) | {1063,1064,1095,2195,3296})-{1}
mu = beta-sum(rho**u for u in support)-2*rho**1063
nu = (beta+4+sum(rho**u for u in range(1013,1023))+sum(rho**u for u in range(1065,1074))+
      rho**2195+rho**3296+(2**51-2)*(rho**4393+rho**5495)+
      (2**65-1)*sum(rho**u for u in range(8792,8805))+(2**19-1)*rho**8805)
kappa = (rho**30+rho**62+rho**1100+rho**2201+rho**8849+
         sum(s*(rho**(4393-u)+rho**(5495-u)) for u,s in enumerate(printed))+
         sum(2**(10+u)*(rho**(4393-x)+rho**(5495-x)) for u,x in enumerate(printed_slots)))
coefficient_hashes = {}
for name, value in [('beta',beta),('K',kappa),('MC',mu),('MF_source',nu)]:
    raw = gzip.decompress((PAYLOAD/f'{name}.bin.gz').read_bytes())
    need(value.to_bytes(len(raw),'little') == raw, ('printed coefficient mismatch',name))
    coefficient_hashes[name] = digest(raw)
need(all(p.read_bytes() == old for p,old in original.items()), 'maintained root equation changed')
print(json.dumps({'status':'EXTERNAL_TEX_PDF_DISPLAY_CHECK_PASS', 'variant':'89', 'graph_rows':len(matches),
    'decimal_selectors':len(printed), 'slot_count':len(printed_slots), 'raw_coefficient_sha256':coefficient_hashes,
    'tex_sha256':digest(tex_bytes), 'pdf_sha256':digest(pdf_bytes),
    'maintained_equation_hashes':{str(p.relative_to(ROOT)):digest(v) for p,v in original.items()},
    'scope':'external PDF extraction and source/finite check; not a Lean parser/file/PDF theorem or iPRA proof'},
    indent=2,sort_keys=True))
