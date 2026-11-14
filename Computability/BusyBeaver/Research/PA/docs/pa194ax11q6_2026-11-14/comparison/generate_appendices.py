#!/usr/bin/env python3
"""Generate compact, linked LaTeX comparison appendices from final CSV ledgers."""
from pathlib import Path
import csv, re

BASE=Path(__file__).resolve().parent
PIN='4be5c6e3a10292a7466f5d3687e3b39615ff049b'

def tex(s):
    s=s.replace('`','').replace('–','--').replace('—','---').replace('≤',' at most ').replace('≥',' at least ')
    replacements={'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}'}
    return ''.join(replacements.get(c,c) for c in s)

def source_url(locator):
    p=locator.split(' | ')[0].split('::JSON')[0].split('!')[0]
    return 'https://github.com/VladimirReshetnikov/ProveIt/blob/'+PIN+'/'+p

def short_delivery(name):
    return name.removesuffix('.zip')

def longtable_start(cols,head,title,label):
    return '\n'.join([
      r'\begingroup',r'\small',r'\setlength{\tabcolsep}{4pt}',
      r'\setlength{\LTleft}{0pt}',r'\setlength{\LTright}{0pt}',
      r'\renewcommand{\arraystretch}{1.08}',
      r'\begin{longtable}{'+cols+'}',
      r'\caption{'+title+r'}\label{'+label+r'}\\',
      r'\toprule',head+r'\\',r'\midrule',r'\endfirsthead',
      r'\multicolumn{'+str(head.count('&')+1)+r'}{l}{\small\itshape Continued from the preceding page.}\\',
      r'\toprule',head+r'\\',r'\midrule',r'\endhead',
      r'\midrule',r'\multicolumn{'+str(head.count('&')+1)+r'}{r}{\small\itshape Continued on the next page.}\\',r'\endfoot',
      r'\bottomrule',r'\endlastfoot'])+'\n'

deliveries=list(csv.DictReader((BASE/'packet_ledger72.csv').open()))
assert len(deliveries)==72
lines=[r'\section{Complete delivery comparison}',
 r'The comparison is pinned to ProveIt commit \texttt{'+PIN[:12]+r'}. The following 72 entries cover all 61 filed PA research packets and all 11 current incoming archives. Each delivery label links to its pinned source. The contribution summaries attribute the claims made in the packets; they do not assert that all historical consistency proofs were independently replayed. The accompanying CSV and JSON ledger preserve full paths, hashes, and source URLs.',
 longtable_start(r'@{}>{\raggedright\arraybackslash}p{.045\linewidth}>{\raggedright\arraybackslash}p{.315\linewidth}>{\raggedright\arraybackslash}p{.59\linewidth}@{}',r'No. & Delivery & Contribution and limit','All 72 research deliveries','tab:all-deliveries')]
for i,r in enumerate(deliveries,1):
    name=short_delivery(r['delivery'])
    link=r'\href{'+r['source_url']+r'}{\nolinkurl{'+name+r'}}'
    location='Incoming archive' if r['location']=='incoming' else 'Filed packet'
    lines.append(str(i)+' & '+link+r'\newline {\footnotesize '+location+'} & '+tex(r['summary'])+r'\\[3pt]')
lines += [r'\end{longtable}',r'\endgroup','']
(BASE/'appendix_deliveries.tex').write_text('\n'.join(lines))

frontier=list(csv.DictReader((BASE/'frontier194_current.csv').open()))
assert len(frontier)==82
rank={'supported packet construction':0,'supplementary construction':1,'research auxiliary':2,'research seed':2,'rejected':3}
labels={'supported packet construction':'Reported','supplementary construction':'Supplementary','research auxiliary':'Research','research seed':'Research seed','rejected':'Rejected'}
frontier.sort(key=lambda r:(rank[r['historical_status']],r['name'].casefold()))
lines=[r'\section{All existing 194-state graph classes}',
 r'The fresh scan recognizes 82 complete one-halt 194-state graphs having a spanning root, modulo working-state renaming. The ledger contains 40 reported constructions, 7 supplementary constructions, 29 research auxiliaries or seeds, and 6 rejected designs. These labels describe the supplied evidence. In particular, Reported does not mean a newly checked end-to-end PA, iPRA, Lean, or Rocq theorem. Click a machine name for one pinned source; the CSV ledger supplies every recognized source locator. The short fingerprint identifies the exact table class. The new candidate is excluded from this historical comparison set.',
 longtable_start(r'@{}>{\raggedright\arraybackslash}p{.04\linewidth}>{\raggedright\arraybackslash}p{.255\linewidth}>{\raggedright\arraybackslash}p{.14\linewidth}>{\raggedright\arraybackslash}p{.495\linewidth}@{}',r'No. & Machine / class & Evidence label & Distinguishing mechanism','All 82 existing 194-state classes','tab:frontier194')]
for i,r in enumerate(frontier,1):
    name=r'\href{'+source_url(r['source_locators'])+'}{'+tex(r['name'])+'}'
    name+=r'\newline {\footnotesize\texttt{'+r['graph_class_sha256'][:12]+'}}'
    lines.append(str(i)+' & '+name+' & '+labels[r['historical_status']]+' & '+tex(r['mechanism'])+r'\\[3pt]')
lines += [r'\end{longtable}',r'\endgroup','']
(BASE/'appendix_frontier194.tex').write_text('\n'.join(lines))
print('Generated appendices for',len(deliveries),'deliveries and',len(frontier),'194-state classes.')
