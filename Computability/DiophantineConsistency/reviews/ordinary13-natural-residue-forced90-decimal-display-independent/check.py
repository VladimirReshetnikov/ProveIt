#!/usr/bin/env python3
"""Independent compact decimal source, graph and extracted PDF review."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary13-natural-residue-forced90-decimal-display'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b
t=pin(P/'equation.tex','5977cd5e523fec17943f317caa967f18a2781dd6e31922121496c88041fd1c55').decode()
pdf=pin(P/'equation.pdf','877dc80f4fc95ef81004e29d519d8e7debed058eee08d877171d791611017bed')
r=json.loads(pin(P/'result.json','9d58217a6134e4f6bd6202c5b9b550c78fd2dcfe8a915c16fffadbaf2fc3248a'))
z=json.loads(pin(P/'render-result.json','34e596190b083b334475f7f62c1c4e170dd8c95d148da9f9f7e18ea2b534a60b'))
g=json.loads(pin(D/'research/ordinary13-natural-residue-forced90-degree56/candidate.json','e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'))
prior=pin(D/'research/ordinary14-natural79-decimal-render-candidate/equation.tex','a9a6ae35d88e3f842d5493fbe6c7f6460285a3d3ae211a40c6b0375ae350ec20').decode()
seed=pin(D/'research/ordinary14-natural79-decimal-render-candidate/DECIMAL_SEED.txt','8c85329f040c7a4d41d521deee0dec970191ff59e08ccf5487e32655dc09a297').decode().strip()
ind=D/'reviews/ordinary14-natural79-decimal-render-independent/check.py';pin(ind,'b4c66cf5ee65e5be6af328dbd52df98296c6b81355120820509d0d5b31ddc7a2')
pin(D/'reviews/ordinary13-natural-residue-forced90-independent/result.json','d4cfc1fa4f40cbd6e308814640151b2c954d99487889fe2c91733bd05b8bf97c')
old=json.loads(subprocess.run([sys.executable,'-I','-S','-B',str(ind)],capture_output=True,text=True,check=True).stdout)
assert old['beta_added_to_MF_exactly_once'] and old['decimal_digits']==15086
names=r['input_names'];assert len(names)==len(set(names))==len(g['witnesses'])==13 and all(re.fullmatch(r'arg[A-Za-z0-9]+',n) for n in names)
listed=[]
for item in re.findall(r'\\noindent\\texttt\{([^}]*)\}\\par',t):listed.extend(x.strip() for x in item.split(','))
assert listed==names and 'distinct nonnegative integers' in t
alias={row[0]:f'G{i:03d}' for i,row in enumerate(g['source'],1)};ins=dict(zip(g['witnesses'],names));texports={'beta':r'\beta','K0':'K','MC':r'\mu','MF':r'\omega'};pdfports={'beta':'β','K0':'K','MC':'µ','MF':'ω'}
def term(x):
 if type(x) is int:return str(x)
 if x in texports:return texports[x]
 return r'\mathtt{'+(ins[x] if x in ins else alias[x])+'}'
def plain(x):
 if type(x) is int:return str(x)
 return pdfports[x] if x in pdfports else ins[x] if x in ins else alias[x]
want=[r'\noindent $'+term(n)+'='+term(a)+{'*':r'\cdot ','+':'+','-':'-'}[op]+term(b)+r'$\par' for n,op,a,b in g['source']]
rows=t.split('% BEGIN GATE GRAPH\n',1)[1].split('\n% END GATE GRAPH',1)[0].splitlines();assert len(rows)==90 and rows==want and r'\boxed{\mathtt{G090}=0}' in t
marker=r'\bigskip\textbf{The four fixed integers.}'
constants=lambda x:marker+x.split(marker,1)[1].split(r'\endgroup',1)[0]+r'\endgroup'
assert constants(t)==constants(prior) and hashlib.sha256(constants(t).encode()).hexdigest()==r['constant_section_sha256']
assert 'ordinary base-10 notation' in constants(t) and r'\rho=2^{67}' in constants(t)
part=constants(t).split(r'\par\begingroup\fontsize{6}{7}\selectfont\ttfamily',1)[1].split(r'\endgroup',1)[0]
assert ''.join(x[:-4] for x in part.splitlines() if x.strip())==seed and len(seed)==15086
info=subprocess.run(['pdfinfo',str(P/'equation.pdf')],capture_output=True,text=True,check=True).stdout;assert re.search(r'^Pages:\s+4\s*$',info,re.M)
text=subprocess.run(['pdftotext','-layout',str(P/'equation.pdf'),'-'],capture_output=True,text=True,check=True).stdout
pattern=r'\b(G\d{3})\s*=\s*([A-Za-z0-9βµω]+)\s*([+−·])\s*([A-Za-z0-9βµω]+)'
found=re.findall(pattern,text);wantpdf=[(alias[n],plain(a),{'*':'·','+':'+','-':'−'}[op],plain(b)) for n,op,a,b in g['source']]
assert len(found)==90 and len({x[0] for x in found})==90 and sorted(found)==sorted(wantpdf)
raw=subprocess.run(['pdftotext','-raw',str(P/'equation.pdf'),'-'],capture_output=True,text=True,check=True).stdout
assert 'external standard-integer argument' in t and 'nonstandard model transfer and iPRA endpoint remain open' in t
assert 'external standard-integer argument' in ' '.join(raw.split()) and 'nonstandard model transfer and iPRA endpoint remain open' in ' '.join(raw.split())
seedpdf=raw.split('Complete decimal integer P.',1)[1].split('The compact fixed-port recipe',1)[0]
assert ''.join(x.strip() for x in seedpdf.splitlines() if re.fullmatch(r'\d{1,75}',x.strip()))==seed
assert 'Overfull' not in (P/'equation.log').read_text() and z['pdf_sha256']==hashlib.sha256(pdf).hexdigest()
print(json.dumps({'scope':'compact graph/TeX/PDF and inherited P72/P115 byte checks; no Lean or formal PDF semantics','nonnegative_variables':13,'graph_rows':90,'decimal_seed_digits':15086,'pdf_pages':4,'distinct_port_tuple_from_current2011':True,'recipe_exactly_matches_independently_recomputed_compact_ports':True,'graph_p72_p115_receipt_pinned':True},sort_keys=True,indent=2))
