#!/usr/bin/env python3
"""Source/byte-checked draft TeX only; no Lean, PDF, existing-page mutation."""
from pathlib import Path
import ast,gzip,hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(rel,h):
 b=(D/rel).read_bytes();assert hashlib.sha256(b).hexdigest()==h,(rel,hashlib.sha256(b).hexdigest());return b
G=json.loads(pin('research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'))
graph=pin('research/ordinary14-natural79-corrected-reflection-overlay/source/P79NaturalForcedW.lean.src','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36').decode()
endpoint=pin('research/ordinary14-natural79-corrected-reflection-overlay/source/Natural79Endpoint.lean.src','9b527ff7a8b6e166869f2565b83a8c37956680d538c49557de9c82ea1a6041e6').decode()
modeliff=pin('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean','379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46').decode()
assert 'def expression : Expr (Fin 14) := (P79NaturalForcedW.graph CompactSymbolicModelIff.p).output' in endpoint
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in modeliff
rows=pin('Lean/DiophantineConsistency/Compact44/Compact943Data.lean','10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8').decode()
kern=pin('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernel.lean','9b2b73430cbf4578ef4b4c7d4658c9526b7ebdc423263470df907a16b454ba55').decode()
param=pin('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernelOpaque.lean','8ae9ed11d9e7408e4fd71555569181b0fb785f24f3177facc6c6c997d0d5e615').decode()
mass=pin('Lean/DiophantineConsistency/Compact44/CompactCoefficientMass.lean','1dad41ebf3fe6c9c68b6f6d76bd6d1a42f318ca75eb6f107d3bcd0407246b592').decode()
mask=pin('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean','f93993e8b4badb6518d8ac6e575d406f322d7205b7d95c17c185103510b474c2').decode()
highsrc=pin('Lean/DiophantineConsistency/Compact44/CompactHighPopulation.lean','b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d').decode()
portsrc=pin('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean','0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414').decode()
fixed=pin('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean','bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea').decode()
binding=json.loads(pin('con-zfc-diophantine-forms/72-congruence-sextic/positive13/ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
# The exact source graph is compared structurally, not only by samples.
block=graph.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('-- END LITERAL GRAPH',1)[0];prog=ast.parse('\n'.join(x.strip()[4:].replace(':=','=') for x in block.splitlines() if x.strip()))
ops={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'};actual=[]
def arg(x):
 if isinstance(x,ast.Name):return x.id
 assert isinstance(x,ast.Constant) and type(x.value)==int and x.value>=0;return x.value
for x in prog.body:
 assert isinstance(x,ast.Assign) and len(x.targets)==1 and isinstance(x.targets[0],ast.Name) and isinstance(x.value,ast.BinOp) and type(x.value.op) in ops
 actual.append([x.targets[0].id,ops[type(x.value.op)],arg(x.value.left),arg(x.value.right)])
assert len(actual)==G['operations']==79 and actual==G['source'] and G['output']=='out'
unknowns=['J','F','A','f','i','T','w','s','r','e','z','y','g','h'];assert len(set(unknowns))==14
assert G['witnesses']==['n_J','n_F','n_alpha','n_f','n_i','n_T','n_w','n_s','n_r','n_eta','n_zeta','n_y','n_gamma','n_h']
for i,n in enumerate(G['witnesses']):assert f'let {n} : Expr (Fin 14) := .var {i}' in graph
for i,n in enumerate(G['fixed_numerals']):assert f'let {n} : Expr (Fin 14) := .constant (p {i})' in graph
assert '⟨F0, F1, Fa, Fs, guard, out, qF, C, G, R⟩' in graph
# Source-explicit compact tuple. All computations remain external checks.
assert 'def betaNat : ℕ := 2^(67*8807)-1' in fixed
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in portsrc
assert 'def selector (t : Nat × Nat × Nat × Nat) : Nat := 1 + 2^10 * (2^41 - value t)' in mass
assert 't.1 + 2^8*t.2.1 + 2^17*t.2.2.1 + 2^25*t.2.2.2 + 127*2^34' in mass and 'r^8807*r^42' in param
assert '((range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032 ∪' in mask and '{1063,1064,1095,2195,3296}) \\ {1})' in mask
inside=rows.split('-- BEGIN PINNED ORDERED ROWS\n',1)[1].split('\n-- END PINNED ORDERED ROWS',1)[0]
table=[]
for line in inside.splitlines():
 m=re.fullmatch(r'  \((\d+), (\d+), (\d+), (\d+)\),?',line);assert m;table.append(tuple(map(int,m.groups())))
assert len(table)==943
m=re.search(r'^def slots : List ℕ := \[([0-9,]+)\]$',kern,re.M);assert m;slots=list(map(int,m.group(1).split(',')));assert len(slots)==41
weights=[]
for a,b,c,d in table:
 value=a+2**8*b+2**17*c+2**25*d+127*2**34;assert 0<=value<=2**41
 weight=1+2**10*(2**41-value);assert 0<weight<10**16;weights.append(weight)
payload=''.join(f'{x:016d}' for x in reversed(weights)).lstrip('0');assert payload
padded=payload.zfill(16*943);assert [int(padded[-16*(i+1):len(padded)-16*i if i else None]) for i in range(943)]==weights
B=1<<67;beta=(1<<(67*8807))-1
K=sum(1<<(67*i) for i in (30,62,1100,2201,8849))
for i,c in enumerate(weights):K+=c*((1<<(67*(4393-i)))+(1<<(67*(5495-i))))
for i,j in enumerate(slots):K+=(1<<(10+i))*((1<<(67*(4393-j)))+(1<<(67*(5495-j))))
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
low=beta-sum(1<<(67*j) for j in support)-2*(1<<(67*1063))
highpart=highsrc.split('def highDigits : List ℕ :=',1)[1].split('\ntheorem digits_length',1)[0]
expected='[4] ++ List.replicate 1012 0 ++ List.replicate 10 1 ++\n  List.replicate 42 0 ++ List.replicate 9 1 ++\n  List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1] ++\n  List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu] ++\n  List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]'
assert highpart.strip()==expected and 'def mu : ℕ := 2^51-2' in highsrc and 'def padding : ℕ := 2^65-1' in highsrc and 'def lastPadding : ℕ := 2^19-1' in highsrc
high=[4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[2**51-2]+[0]*1101+[2**51-2]+[0]*3296+[2**65-1]*13+[2**19-1,0];assert len(high)==8807
highval=sum(d<<(67*i) for i,d in enumerate(high) if d);MF=beta+highval
computed={'beta':beta,'K0':K,'MC':low,'MF':MF};rawhash={}
for n,meta in binding['ports'].items():
 data=(D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'/meta['path']).read_bytes();assert hashlib.sha256(data).hexdigest()==meta['sha256_gzip']
 raw=gzip.decompress(data);assert len(raw)==meta['raw_bytes'] and hashlib.sha256(raw).hexdigest()==meta['sha256_raw'] and int.from_bytes(raw,'little')==computed[n];rawhash[n]=meta['sha256_raw']
# Render 79 literal assignments with visibly distinct input letters and
# monospaced graph-abbreviation names. No TeX/PDF execution.
input_names=dict(zip(G['witnesses'],unknowns));port_names={'beta':r'\beta','K0':'K','MC':r'\mu','MF':r'\omega'}
def tex_name(n):
 if type(n)==int:return str(n)
 if n in input_names:return input_names[n]
 if n in port_names:return port_names[n]
 return r'\mathtt{v'+n.replace('_',r'\_')+'}'
lines=[r'\noindent $'+tex_name(n)+' = '+tex_name(a)+({'*':r'\cdot ', '+':'+', '-':'-'}[op])+tex_name(b)+r'$\par' for n,op,a,b in actual]
runs=[];i=0
while i<len(high):
 if high[i]==0:i+=1;continue
 j=i+1
 while j<len(high) and high[j]==high[i]:j+=1
 runs.append((i,j-1,high[i]));i=j
assert runs==[(0,0,4),(1013,1022,1),(1065,1073,1),(2195,2195,1),(3296,3296,1),(4393,4393,2**51-2),(5495,5495,2**51-2),(8792,8804,2**65-1),(8805,8805,2**19-1)]
tex=r'''\documentclass[10pt]{article}
\usepackage[margin=.55in]{geometry}
\usepackage{amsmath,amssymb,multicol}
\pdfinfoomitdate=1\pdftrailerid{}
\pagestyle{empty}\setlength{\parindent}{0pt}
\begin{document}
\begin{center}{\Large Natural-79 equation: source-only candidate}\\
Fourteen nonnegative integer unknowns; 79 binary-operation abbreviations.
\end{center}
The unknowns, all distinct, are $J,F,A,f,i,T,w,s,r,e,z,y,g,h\in\mathbb N$.
All monospaced names below are polynomial abbreviations, and $\beta,K,\mu,\omega$ are fixed integers defined later.
\begin{multicols}{3}\small
'''+ '\n'.join(lines)+r'''
\end{multicols}
The single equation is $\boxed{\mathtt{vout}=0}$.

\bigskip\textbf{The four fixed integers.} All numerals, including the complete seed below, use ordinary base-10 notation. Put $\rho=2^{67}$, $\beta=\rho^{8807}-1$, and let $d_j=\lfloor P/10^{16j}\rfloor\bmod 10^{16}$ for $0\le j<943$.
Let the ordered list $(\lambda_0,\ldots,\lambda_{40})$ be
\[\begin{gathered}
'''+((','+chr(92)*2+chr(10)).join(','.join(map(str,slots[j:j+14])) for j in range(0,len(slots),14)))+r'''
\end{gathered}\]
Define
\[\begin{split}
K={}&\rho^{30}+\rho^{62}+\rho^{1100}+\rho^{2201}+\rho^{8849}\\
&+\sum_{j=0}^{942}d_j(\rho^{4393-j}+\rho^{5495-j})\\
&+\sum_{j=0}^{40}2^{10+j}(\rho^{4393-\lambda_j}+\rho^{5495-\lambda_j}).
\end{split}\]
For integer intervals $[a,b]=\{a,a+1,\ldots,b\}$, let
\[\begin{split}S={}&([0,942]\cup[983,992]\cup[1003,1011]\cup[1013,1031]\\&{}\cup\{1063,1064,1095,2195,3296\})\setminus\{1\}.\end{split}\]
Put $\mu=\beta-\sum_{k\in S}\rho^k-2\rho^{1063}$ and $\omega=\beta+H$, where
\[\begin{split}
H={}&4+\sum_{k=1013}^{1022}\rho^k+\sum_{k=1065}^{1073}\rho^k+\rho^{2195}+\rho^{3296}\\
&+(2^{51}-2)(\rho^{4393}+\rho^{5495})+(2^{65}-1)\sum_{k=8792}^{8804}\rho^k+(2^{19}-1)\rho^{8805}.
\end{split}\]

\bigskip\textbf{Complete decimal integer $P$.} Concatenate these lines in order, without spaces or line breaks:
\par\begingroup\fontsize{6}{7}\selectfont\ttfamily
'''+ '\n'.join(payload[j:j+75]+r'\par' for j in range(0,len(payload),75))+r'''
\endgroup
\par\small This is an unelaborated source-mapping draft; it is not a claim that the equation or its iPRA equivalence has been checked by Lean.
\end{document}
'''
assert set(payload)<=set('0123456789') and 'base 61' not in tex.lower()
(P/'equation.tex').write_text(tex)
(P/'DECIMAL_SEED.txt').write_text(payload+'\n')
report={'scope':'external exact source-row and compact symbolic-port transcription versus retained coefficient bytes; no Lean or PDF','graph_rows':79,'input_names':unknowns,'decimal_seed_digits':len(payload),'decimal_seed_sha256':hashlib.sha256(payload.encode()).hexdigest(),'port_values_match_retained_gzip_bytes':rawhash,'fixed_mf_shifted_once':True,'tex_sha256':hashlib.sha256(tex.encode()).hexdigest(),'output':'research/ordinary14-natural79-decimal-render-candidate/equation.tex'}
(P/'result.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
print(json.dumps(report,sort_keys=True,indent=2))
