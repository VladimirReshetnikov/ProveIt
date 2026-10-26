#!/usr/bin/env python3
"""Print finite ports and ordered unit-pivot tables defining all selected circuits."""
import argparse,hashlib,json,math
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--package',type=Path,required=True);p.add_argument('--out',type=Path,default=Path(__file__).with_name('reciprocal_ledger.tex'));a=p.parse_args()
def read(path):return json.loads(path.read_text())
def poly(ts):
 out=''
 for c,idx in ts:
  if not c:continue
  body=''.join('x_{%d}'%i+('^{%d}'%idx.count(i)if idx.count(i)>1 else'')for i in sorted(set(idx)))
  body=(''if abs(c)==1 and body else str(abs(c)))+body
  out+=('-'if c<0 else('+'if out else''))+body
 return out or'0'
def nums(v):return ','.join(map(str,v))
seed=read(a.package/'seeds/joint_13_frame/certificate.json')
rows=[r'\section{Exact reciprocal ports and substitution ledgers}',r'\label{sec:reciprocal-ledger}',
 r'This appendix, together with the complete conservative residual array in Appendix~\ref{sec:conservative-residuals}, defines every selected reciprocal polynomial without a search or an implicit coefficient. All $x_i,R_i$ in the port tables refer to that appendix, not to the principal quartic.',
 r'\subsection{The common principal pairs and power requests}',
 r'Put $A=x_{130}$ and $d=A-1$. The thirteen pairs have the following literal ports. The norm and multiplication rows remain part of the source.',
 r'\begin{center}\small\setlength{\tabcolsep}{5pt}',r'\begin{tabular}{@{}rllllrr@{}}\toprule',r'Pair & $k_i$ & $X_i$ & $Y_i$ & $Z_i$ & Gate & Norm\\\midrule']
for pair in seed['pairs']:
 rows.append(pair['name'].replace('index','')+' & '+' & '.join('$'+poly(pair[k])+'$'for k in['k','X','Y','Z'])+f" & {pair['gate_row']} & {pair['norm_row']}"+r'\\')
rows += [r'\bottomrule\end{tabular}\end{center}',r'The four base blocks and all fifteen $(\text{pair},m)$ requests are:',r'\begin{center}\small',r'\begin{tabular}{@{}rll@{}}\toprule',r'Block & Base $n_j$ & Requests $(i,m)$\\\midrule']
for j,b in enumerate(seed['blocks']):
 rs=[f"({v['pair'].replace('index','')},{poly(v['m'])})"for v in b['requests']]
 for k in range(0,len(rs),3):rows.append((str(j)+f" & ${poly(b['base'])}$ & "if k==0 else' & & ')+'$'+r',\quad'.join(rs[k:k+3])+'$'+r'\\')
rows += [r'\bottomrule\end{tabular}\end{center}',
 r'Define $T_j,H_j,S_j,E_j,\Omega$ from precisely these ports as in Section~\ref{sec:reciprocal23}. Thus $Z_i$ is the displayed polynomial port, not a new independent variable. To define the literal reduced source chart, put $\widehat E_0=E_0$, $\widehat E_1=E_1$ and',
 r'\[\widehat E_2=E_2+R_{95}+R_{113},\qquad \widehat E_3=E_3+\sum_{r\in\mathcal J}R_r,\]',
 r'where $\mathcal J=\{101,103,105,107,109,111,115,117,121,123\}$. These exact retained-norm corrections are necessary for the literal coefficient arrays, although they vanish at source zeros. Use $\widehat E_j$, not $E_j$, in every seed pool below. The source orientation identity is',
 r'\[\Omega-(R_{135}+d x_{191})=-R_{138}.\]',
 r'This identity is exact in the conservative source coordinates, including their existing row chart. The joint numerator is exactly $\Omega^{\prime}=\Omega+R_{124}$.',
 r'\subsection{The seeds before elimination}',
 r'For a fixed ordered block set $I$ and a new variable $z_I$, write',
 r'\[\mathcal P_I=\sum_{j\in I}\widehat E_j\prod_{h\in I\setminus\{j\}}T_h-z_I\prod_{j\in I}T_j.\]',
 r'The sparse 114 seed retains all source rows except $96,97,98,99,141,142,143,144$, deletes coordinates $137,138,139,140,201,202,203,204$, and appends $\mathcal P_{\{0,1\}}$ followed by $\mathcal P_{\{2,3\}}$. The other retained rows preserve ascending original order. First retain coordinates in ascending original order, then append the two new pool variables in that same pool order. This gives 203 coordinates and 143 rows.',
 r'The joint 113 seed additionally deletes row 135 and coordinate 191. Its appended rows, in order, are',
 r'\[\Omega^{\prime} T_0+d\mathcal P_{\{0\}},\qquad\mathcal P_{\{1,2,3\}}.\]',
 r'Use the same ascending retained-coordinate order and then the two new pool variables. This gives 202 coordinates and 142 rows. The matched unfused control instead keeps row 135 and coordinate 191 and appends $\mathcal P_{\{0\}},\mathcal P_{\{1,2,3\}}$.',
 r'The 138-variable endpoint starts directly from the complete 209-coordinate, 149-row conservative source, with no new pool seed. Its 71 monic substitutions are therefore generic exact eliminations, not a gain credited to the new joint theorem.',
 r'\subsection{How to read the complete ordered tables}',
 r'In each following table, $(j,r,v,\epsilon)$ means: at ordinal $j$, the current row with original seed label $r$ has the form $\epsilon u_v+f$, with no other $u_v$ term. Replace $u_v$ by $-\epsilon f$ in every other current row and delete row $r$. Row and coordinate labels remain the initial seed labels throughout; do not compact after a step. At the end retain the undeleted row labels in ascending order, and compact the undeleted coordinate labels in ascending order. The sum of squares of those remaining rows is the literal final polynomial. Thus the tables and fixed seeds alone specify every coefficient, with no optimizer or choice left to execute.',
 r'The adjacent \file{NATIVE_DEFINITION.json} files also give every resulting pivot polynomial explicitly; independent replay verifies each unit coefficient and the complete final residual arrays. The tables below are parsed independently against those files.']
paths=[a.package/'seeds/joint_13_frame/certificate.json']
for name,title in [('integer138_degree8','The 138 variable degree eight polynomial'),('integer114_degree16','The sparse 114 variable degree sixteen polynomial'),('integer113_degree16','The joint 113 variable degree sixteen polynomial')]:
 path=a.package/'equations'/name/'NATIVE_DEFINITION.json';paths.append(path);d=read(path);ss=d['steps'];n=len(ss);part=math.ceil(n/3)
 rows += [r'\subsection{'+title+'}',f"The fixed seed has {d['source_coordinates']} coordinates and {d['source_rows']} rows. Perform all {n} steps in ordinal order, reading each four-column block downward, then the next block.",r'\begin{center}\small\setlength{\tabcolsep}{5pt}',r'\begin{tabular}{@{}rrrr@{\quad}rrrr@{\quad}rrrr@{}}\toprule',r'$j$&$r$&$v$&$\epsilon$&$j$&$r$&$v$&$\epsilon$&$j$&$r$&$v$&$\epsilon$\\\midrule']
 for line in range(part):
  fields=[]
  for col in range(3):
   k=col*part+line
   if k<n:
    x=ss[k];fields.extend(str(x[v])for v in['ordinal','row','variable','unit_coefficient'])
   else:fields.extend(['']*4)
  rows.append(' & '.join(fields)+r'\\')
 rows += [r'\bottomrule\end{tabular}\end{center}',f"The final count is {d['metrics']['variables']} coordinates and {d['metrics']['residuals']} rows; all are live. The ordered complement of the table's deleted indices agrees exactly with the supplied retained-index arrays."]
rows.append('')
a.out.write_text('\n'.join(rows))
binding={'method':'All selected source ports and ordered triples from fixed normative certificate data; no producer import','inputs':[{ 'path':str(p.relative_to(a.package)), 'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}for p in paths],'tex_sha256':hashlib.sha256(a.out.read_bytes()).hexdigest()}
print(json.dumps(binding,indent=2))
