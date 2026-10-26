#!/usr/bin/env python3
"""Typeset the frozen comparison inventory without treating absent metrics as zero."""
import json,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SRC=ROOT.parent/'audit/INPUT_COMPARISON.json'
d=json.loads(SRC.read_text())
short={'AffineHorizonsCenteredCertificates':'Affine horizons','CofinalPellCompression':'Cofinal Pell','DiagonalGrowth':'Diagonal growth','DirectIntegerElimination':'Direct elimination','MixedBasePooling':'Mixed base','PellCarrier65':'Pell carrier 65','PellGrowth210':'Pell growth 210','SignedHorizonsResidueCarriers':'Signed horizons','CRTAnchorsRound22':'Round22','175-exact-contractions':'175 contractions','176-oriented-pooling':'176 oriented pool','177-oriented-powers':'177 oriented powers','178-polynomial-centers':'178 centers'}
dom={'positive_integers':r'$\Z_{>0}$','nonnegative_integers':r'$\N$','unrestricted_integers':r'$\Z$'}
def num(x):
 if x is None:return '--'
 if x==2**40:return '$2^{40}$'
 return str(x)
def status(source,p):
 if source=='PellGrowth210' and p['name']!='compact11':return 'C,R'
 if source=='DiagonalGrowth':return 'C'
 if source=='AffineHorizonsCenteredCertificates':return 'R'
 if source=='CRTAnchorsRound22':return 'I'
 return 'S'
def title(p):return p['name'].replace('_',' ')
lines=[r'\subsection{Incoming explicit array controls}',
'The table records the selected array-style controls from all nine incoming',
'archives and sources 175--178. A dash means unreported here, not zero.',
'All entries are inherited comparison inputs, not new Round23 endpoints.',
'\n',r'\begingroup\scriptsize\setlength{\tabcolsep}{4pt}',
r'\begin{longtable}{@{}p{43mm}crrrrl@{}}',r'\toprule',r'Source and chart & Domain & $n$ & Degree & Terms & Height & Evidence\\\midrule\endfirsthead',r'\toprule Source and chart & Domain & $n$ & Degree & Terms & Height & Evidence\\\midrule\endhead',r'\bottomrule\endfoot']
for src in d['sources']:
 for p in src['profiles']:
  if 'live_binary_operations' in p and 'collected_monomials' not in p:continue
  h=p.get('expanded_coefficient_height',{}).get('value')
  lines.append(f"{short[src['source']]} / {title(p)} & {dom[p['domain']]} & {p['variables']} & {p['total_degree']['value']} & {num(p.get('collected_monomials'))} & {num(h)} & {status(src['source'],p)}"+r'\\')
lines += [r'\end{longtable}\endgroup',r'\subsection{Incoming circuit controls}',r'\begingroup\small\setlength{\tabcolsep}{5pt}',r'\begin{longtable}{@{}p{66mm}crrrl@{}}',r'\toprule Source and chart & Domain & $n$ & Degree & Gates & Evidence\\\midrule\endfirsthead',r'\toprule Source and chart & Domain & $n$ & Degree & Gates & Evidence\\\midrule\endhead',r'\bottomrule\endfoot']
for src in d['sources']:
 for p in src['profiles']:
  if 'live_binary_operations' not in p:continue
  lines.append(f"{short[src['source']]} / {title(p)} & {dom[p['domain']]} & {p['variables']} & {p['total_degree']['value']} & {p['live_binary_operations']} & {status(src['source'],p)}"+r'\\')
lines += [r'\end{longtable}\endgroup','']
(ROOT/'comparison_tables.tex').write_text('\n'.join(lines))
(ROOT/'COMPARISON_BINDING.json').write_text(json.dumps({'source':str(SRC.relative_to(ROOT.parent)),'source_sha256':hashlib.sha256(SRC.read_bytes()).hexdigest(),'tex_sha256':hashlib.sha256((ROOT/'comparison_tables.tex').read_bytes()).hexdigest(),'sources':len(d['sources']),'profiles':sum(len(s['profiles'])for s in d['sources'])},indent=2)+'\n')
