#!/usr/bin/env python3
"""Independent read-only graph, source/TeX/PDF and seed check; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/adaptive-aq17-positive-bindings95-decimal-display'
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(str(p),sha(b));return b
tex=pin(P/'equation.tex','de49f7220bdaa6e19a28538494330cd9ddae768af6c65b00e35dc530c3065c1c').decode()
pdf=pin(P/'equation.pdf','abcbd6966273007ac9bed71250675f4ff878426ad96f5dbdd00974301bd7eb02')
report=json.loads(pin(P/'result.json','d7d0ff80859af02c08e23353a274be7d01c7f1b91a28c3284f103fbffe0334ed'))
render=json.loads(pin(P/'render-result.json','612457329711cef52565bf4fbc7e5b2e0992d78acfb157f9b25601dee4916b1e'))
g=json.loads(pin(D/'research/adaptive-aq17-positive-bindings95/candidate.json','624cc7848f1f36db2d35f5fdfc37111e36ab8e3e8c0ee71553c4fda6739de4fc'))
orig=pin(D/'equation.tex','94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635').decode()
seedsource=pin(D/'Lean/DiophantineConsistency/DecimalMachine215.lean','00e46d6917bb18090027bece970a7ad1bc6eb691bd35c682d4be1a5332f82f80').decode()
mask=pin(D/'Lean/DiophantineConsistency/CurrentMaskData2011.lean','8e92c1f507bc250c31fb2671a921dfbef7a44ba643956f962cd64d9b50bd4582').decode()
kdata=pin(D/'Lean/DiophantineConsistency/CurrentKernelData2011.lean','529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c').decode()
native=pin(D/'Lean/DiophantineConsistency/IPRAAQ22Native.lean','b90a9eb67b6fef945e6f1a3c9900e39e3a07a16dbe032089b3489660e00ce747').decode()
historical=json.loads(pin(D/'reviews/equation14-historical-literal-binding-independent/receipt.json','5a447f8fcebc2065851110ddb2d68afb4c660b49602e2c6be6c69088380fa06c'))
assert len(g['source'])==95 and len(g['witnesses'])==17 and report['domain']=='positive integers'
short=report['unknowns'];assert len(short)==len(set(short))==17 and all(re.fullmatch(r'arg[A-Za-z0-9]+',n) for n in short)
listed=[]
for x in re.findall(r'\\noindent\\texttt\{([^}]*)\}\\par',tex):listed.extend(y.strip() for y in x.split(','))
assert listed==short and 'each a positive integer' in tex
witness=dict(zip(g['witnesses'],short));alias={n:f'G{i:03d}' for i,(n,_,_,_) in enumerate(g['source'],1)}
assert len(alias)==95 and set(alias.values()).isdisjoint(short)
ports={'beta':r'\beta','K0':'K','MC':r'\mu','MF':r'\omega'}
def term(x):
 if type(x)==int:return str(x)
 if x in ports:return ports[x]
 return r'\mathtt{'+(witness[x] if x in witness else alias[x])+'}'
expected=[r'\noindent $'+term(n)+'='+term(x)+{'*':r'\cdot ','+':'+','-':'-'}[op]+term(y)+r'$\par' for n,op,x,y in g['source']]
rows=tex.split('% BEGIN GATE GRAPH\n',1)[1].split('\n% END GATE GRAPH',1)[0].splitlines()
assert rows==expected and r'\boxed{\mathtt{G095}=0}' in tex
start=r'\textbf{The four fixed integers.}'
constants=lambda t:start+t.split(start,1)[1].split(r'\endgroup',1)[0]+r'\endgroup'
assert constants(tex)==constants(orig) and sha(constants(tex).encode())==report['constants_section_sha256']
for macro in [r'\newcommand{\fl}[1]{\left\lfloor#1\right\rfloor}',r'\newcommand{\rg}[2]{\{#1,\ldots,#2\}}',r'\let\bigsum\sum\renewcommand{\sum}{\bigsum\nolimits}']:
 assert macro in orig and macro in tex
assert r'The integer $\mathcal A$ in base 10.' in constants(tex) and 'base 61' not in constants(tex).lower()
seedpart=constants(tex).split(r'\fontsize{7.7}{8.2}\selectfont\ttfamily',1)[1]
lines=[l[:-4] for l in seedpart.splitlines() if re.fullmatch(r'\d+\\par',l)]
assert len(lines)==12 and [len(x) for x in lines]==[62]*11+[33]
m=re.search(r'^def seed : ℕ := ([0-9]+)$',seedsource,re.M);assert m and ''.join(lines)==m[1] and len(m[1])==715
assert 'def ports : Fin 4 → ℤ := CurrentMasks2011.ports (K : ℤ)' in kdata
assert 'def ports (K : ℤ) : Fin 4 → ℤ := ![beta, K, lowPort, highPort + beta]' in mask
assert '(positiveShift (AdaptiveAQ22Literal.literal CurrentWindowCarry2011.ports))' in native
assert historical['status']=='PASS_INDEPENDENT_FINITE_BINDING_REVIEW' and historical['fresh_probe_exit']==historical['recipe_rerun_exit']==0
assert historical['recipe_tile_rows']==942 and historical['recipe_rank_comparisons']==885481
assert historical['input_sha256'][str(D/'equation.tex')]==sha(orig.encode())
assert historical['input_sha256'][str(D/'Lean/DiophantineConsistency/CurrentKernelData2011.lean')]==sha(kdata.encode())
expected_hash={p['name']:p['integer_sha256'] for p in historical['ports']}
rho=2**47; beta=rho**2011-1
G=lambda n:(rho**n-1)//(rho-1)
low=beta-G(951)-rho**960*G(26)-rho**1004
high=beta+8*G(917)-4+(2**45-4)*rho**1005+rho**960*G(9)+rho**987*G(8)+rho**1004
for n,value in [('beta',beta),('MC',low),('MF',high)]:
 assert sha(value.to_bytes((value.bit_length()+7)//8,'big'))==expected_hash[n],n
recipe_path=D/'research/adaptive-direct-ordinate86/verify_printed_constants86.py'
pin(recipe_path,'102f7d8952434072d71baa6fde95722863d443ed8c26b94f39ec45b4143e32f6')
recipe=json.loads(subprocess.run([sys.executable,'-I','-S','-B',str(recipe_path)],text=True,capture_output=True,check=True).stdout)
assert recipe['result']=='PASS' and recipe['tile_rows']==942 and recipe['rank_comparisons']==885481
assert recipe['constant_block_sha256']==report['constants_section_sha256']
for historical_name,recipe_name in [('beta','beta'),('K0','K'),('MC','MC'),('MF','MF_source')]:
 assert recipe['fixed_port_records'][recipe_name]['sha256']==expected_hash[historical_name],historical_name

info=subprocess.run(['pdfinfo',str(P/'equation.pdf')],text=True,capture_output=True,check=True).stdout
assert re.search(r'^Pages:\s+2\s*$',info,re.M)
raw=subprocess.run(['pdftotext','-raw',str(P/'equation.pdf'),'-'],text=True,capture_output=True,check=True).stdout
pdfrows=[line.strip() for line in raw.splitlines() if re.match(r'^G\d{3}\s*=',line.strip())]
def glyph(x):
 if type(x)==int:return str(x)
 if x in ports:return {'beta':'β','K0':'K','MC':'µ','MF':'ω'}[x]
 return witness[x] if x in witness else alias[x]
want=[' '.join((alias[n]+' = '+glyph(x)+' '+{'*':'·','+':'+','-':'−'}[op]+' '+glyph(y)).split()) for n,op,x,y in g['source']]
assert [' '.join(x.split()) for x in pdfrows]==want
seedpdf=[l.strip() for l in raw.splitlines() if re.fullmatch(r'\d{62}|\d{33}',l.strip())]
assert seedpdf==lines
assert render['pdf_sha256']==sha(pdf) and report['tex_sha256']==sha(tex.encode())
print(json.dumps({'scope':'independent pinned graph/TeX/PDF and inherited fixed-text comparison; no Lean or formal page semantics',
 'tex_sha256':sha(tex.encode()),'pdf_sha256':sha(pdf),'source_graph_sha256':report['graph_sha256'],
 'witness_names':short,'positive_domain':True,'graph_rows_source_tex_pdf':95,'pdf_pages':2,
 'inherited_fixed_section_exact':True,'decimal_seed_lines':12,'decimal_seed_digits':715,
 'printed_seed_matches_lean_numeral_externally':True,'historical_all_four_port_probe_referenced':True,
 'beta_low_high_recomputed_against_historical_hashes':True,
 'historical_manual_recipe_reproduced_all_four':True,
 'parent_symbolic_ports':'CurrentWindowCarry2011.ports','actual_formal_file_binding':False},sort_keys=True,indent=2))
