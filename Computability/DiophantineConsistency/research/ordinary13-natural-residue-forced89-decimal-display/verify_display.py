#!/usr/bin/env python3
"""Compare graph, compact-port recipe, PDF text, and P72/P115 checks; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(str(p),sha(b));return b
g=json.loads(pin(D/'research/ordinary13-natural-residue-forced89-degree56/candidate.json','c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a'))
prior=pin(D/'research/ordinary14-natural79-decimal-render-candidate/equation.tex','a9a6ae35d88e3f842d5493fbe6c7f6460285a3d3ae211a40c6b0375ae350ec20').decode()
seed=pin(D/'research/ordinary14-natural79-decimal-render-candidate/DECIMAL_SEED.txt','8c85329f040c7a4d41d521deee0dec970191ff59e08ccf5487e32655dc09a297').decode().strip()
review=D/'reviews/ordinary14-natural79-decimal-render-independent/check.py';pin(review,'b4c66cf5ee65e5be6af328dbd52df98296c6b81355120820509d0d5b31ddc7a2')
r=subprocess.run([sys.executable,'-I','-S','-B',str(review)],capture_output=True,text=True,check=True);port_review=json.loads(r.stdout)
assert port_review['beta_added_to_MF_exactly_once'] and port_review['decimal_digits']==15086
r=subprocess.run([sys.executable,'-I','-S','-B',str(D/'research/ordinary13-natural-residue-forced89-degree56/check.py')],capture_output=True,text=True,check=True);graph_receipt=json.loads(r.stdout)
assert graph_receipt['compact_port_bounds_checked'] and graph_receipt['operations']==89
report=json.loads((P/'result.json').read_bytes());raw=(P/'equation.tex').read_bytes();assert sha(raw)==report['tex_sha256'];tex=raw.decode()
names=report['input_names'];assert len(names)==len(g['witnesses'])==13 and len(set(names))==13 and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9]*',n) for n in names)
shown=[]
for x in re.findall(r'\\noindent\\texttt\{([^}]*)\}\\par',tex):shown.extend(y.strip() for y in x.split(','))
assert shown==names
alias={r[0]:f'G{i:03d}' for i,r in enumerate(g['source'],1)};ins=dict(zip(g['witnesses'],names));pt={'beta':r'\beta','K0':'K','MC':r'\mu','MF':r'\omega'};pp={'beta':'β','K0':'K','MC':'µ','MF':'ω'}
def t(x):
 if type(x)==int:return str(x)
 if x in ins:return r'\mathtt{'+ins[x]+'}'
 if x in pt:return pt[x]
 return r'\mathtt{'+alias[x]+'}'
def plain(x):
 if type(x)==int:return str(x)
 if x in ins:return ins[x]
 if x in pp:return pp[x]
 return alias[x]
expected=[r'\noindent $'+t(n)+'='+t(a)+({'*':r'\cdot ', '+':'+','-':'-'}[o])+t(b)+r'$\par' for n,o,a,b in g['source']]
block=tex.split('% BEGIN GATE GRAPH\n',1)[1].split('\n% END GATE GRAPH',1)[0].splitlines();assert block==expected and len(block)==89
assert r'\boxed{\mathtt{'+alias[g['output']]+r'}=0}' in tex
marker=r'\bigskip\textbf{The four fixed integers.}'
constants=lambda s:marker+s.split(marker,1)[1].split(r'\endgroup',1)[0]+r'\endgroup'
assert constants(tex)==constants(prior) and sha(constants(tex).encode())==report['constant_section_sha256']
part=constants(tex).split(r'\par\begingroup\fontsize{6}{7}\selectfont\ttfamily',1)[1].split(r'\endgroup',1)[0]
assert ''.join(x[:-4] for x in part.splitlines() if x.strip())==seed
pdf=(P/'equation.pdf').read_bytes();info=subprocess.run(['pdfinfo',str(P/'equation.pdf')],capture_output=True,text=True,check=True).stdout
pages=int(re.search(r'^Pages:\s*(\d+)',info,re.M).group(1));assert pages==4
text=subprocess.run(['pdftotext','-layout',str(P/'equation.pdf'),'-'],capture_output=True,text=True,check=True).stdout
pattern=r'\b(G\d{3})\s*=\s*([A-Za-z0-9βµω]+)\s*([+−·])\s*([A-Za-z0-9βµω]+)'
found=re.findall(pattern,text);epdf=[(alias[n],plain(a),{'*':'·','+':'+','-':'−'}[o],plain(b)) for n,o,a,b in g['source']]
assert len(found)==89 and sorted(found)==sorted(epdf)
rawtext=subprocess.run(['pdftotext','-raw',str(P/'equation.pdf'),'-'],capture_output=True,text=True,check=True).stdout
seedpart=rawtext.split('Complete decimal integer P.',1)[1].split('The compact fixed-port recipe',1)[0]
assert ''.join(x.strip() for x in seedpart.splitlines() if re.fullmatch(r'\d{1,75}',x.strip()))==seed
assert 'Overfull' not in (P/'equation.log').read_text()
print(json.dumps({'scope':'graph/TeX/PDF text with separately reviewed compact recipe and P72/P115 byte checks; no Lean or formal PDF semantics','graph_rows':89,'distinct_natural_inputs':13,'compact_decimal_digits':len(seed),'pdf_pages':pages,'pdf_sha256':sha(pdf),'compact_recipe_equals_independently_reviewed':True,'computed_ports_match_P72_and_P115':True,'beta_added_to_MF_once':True,'overfull_boxes':0},sort_keys=True,indent=2))
