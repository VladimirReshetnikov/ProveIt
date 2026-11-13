#!/usr/bin/env python3
"""Check every TeX/PDF graph row and inherited decimal seed, without Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(p,sha(b));return b
g=json.loads(pin(D/'research/adaptive-aq26-two-quotients122/candidate.json','14c9cac4f3af45c15ec5e6df623c83fcab7581ba042aff34c6614dad890154ae'))
prior=pin(D/'equation.tex','94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635').decode()
report=json.loads((P/'result.json').read_bytes());raw=(P/'equation.tex').read_bytes();assert sha(raw)==report['tex_sha256'];tex=raw.decode()
short=report['unknowns'];assert len(short)==len(g['witnesses'])==26 and len(set(short))==26
assert all(re.fullmatch(r'[A-Za-z][A-Za-z0-9]*',n) for n in short) and not any(re.fullmatch(r'G\d+',n) for n in short)
shown=[]
for x in re.findall(r'\\noindent\\texttt\{([^}]*)\}\\par',tex):shown.extend(y.strip() for y in x.split(','))
assert shown==short
alias={r[0]:f'G{i:03d}' for i,r in enumerate(g['source'],1)};inputs=dict(zip(g['witnesses'],short))
port_tex={'beta':r'\beta','K0':'K','MC':r'\mu','MF':r'\omega'};port_pdf={'beta':'β','K0':'K','MC':'µ','MF':'ω'}
def term(x,ports):
 if type(x)==int:return str(x)
 if x in inputs:return inputs[x]
 if x in ports:return ports[x]
 return alias[x]
def texterm(x):
 if type(x)==int:return str(x)
 if x in inputs:return r'\mathtt{'+inputs[x]+'}'
 if x in port_tex:return port_tex[x]
 return r'\mathtt{'+alias[x]+'}'
expected_tex=[r'\noindent $'+texterm(n)+'='+texterm(a)+({'*':r'\cdot ', '+':'+','-':'-'}[op])+texterm(b)+r'$\par' for n,op,a,b in g['source']]
block=tex.split('% BEGIN GATE GRAPH\n',1)[1].split('\n% END GATE GRAPH',1)[0].splitlines()
assert block==expected_tex and len(block)==122 and g['output']=='add_qSigned'
assert r'\boxed{\mathtt{'+alias[g['output']]+r'}=0}' in tex
start=r'\textbf{The four fixed integers.}'
previous_constants=start+prior.split(start,1)[1].split(r'\endgroup',1)[0]+r'\endgroup'
new_constants=start+tex.split(start,1)[1].split(r'\endgroup',1)[0]+r'\endgroup'
assert previous_constants==new_constants and sha(new_constants.encode())==report['constants_section_sha256']
assert r'The integer $\mathcal A$ in base 10.' in new_constants
seed_part=new_constants.split(r'\fontsize{7.7}{8.2}\selectfont\ttfamily',1)[1].split(r'\endgroup',1)[0]
seed_lines=[line[:-4] for line in seed_part.splitlines() if line.endswith(r'\par')]
assert seed_lines and all(re.fullmatch(r'[0-9]+',line) for line in seed_lines)
pdf=(P/'equation.pdf').read_bytes();info=subprocess.run(['pdfinfo',str(P/'equation.pdf')],check=True,text=True,capture_output=True).stdout
pages=int(re.search(r'^Pages:\s*(\d+)',info,re.M).group(1));assert pages==2
text=subprocess.run(['pdftotext','-layout',str(P/'equation.pdf'),'-'],check=True,text=True,capture_output=True).stdout
pattern=r'\b(G\d{3})\s*=\s*([A-Za-z0-9βµω]+)\s*([+−·])\s*([A-Za-z0-9βµω]+)'
found=re.findall(pattern,text);expected_pdf=[(alias[n],term(a,port_pdf),{'*':'·','+':'+','-':'−'}[op],term(b,port_pdf)) for n,op,a,b in g['source']]
assert len(found)==122 and sorted(found)==sorted(expected_pdf)
assert all(line in text for line in seed_lines)
log=(P/'equation.log').read_text();assert 'Overfull \\hbox' not in log and 'Overfull \\vbox' not in log
print(json.dumps({'scope':'rowwise graph/TeX and extracted PDF text; inherited fixed-constant text, no Lean or formal rendering semantics',
 'graph_rows':122,'distinct_positive_inputs':26,'pdf_pages':pages,'pdf_sha256':sha(pdf),
 'decimal_seed_lines':len(seed_lines),'decimal_seed_digits':sum(map(len,seed_lines)),
 'inherited_constants_byte_equal':True,'pdf_text_gate_rows_match':True,'overfull_boxes':0},sort_keys=True,indent=2))
