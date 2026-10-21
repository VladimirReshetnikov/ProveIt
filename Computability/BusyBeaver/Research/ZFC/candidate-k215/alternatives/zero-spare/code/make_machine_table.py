#!/usr/bin/env python3
"""Generate the report appendix directly from the exact dense table."""
from pathlib import Path
import argparse
ROOT=Path(__file__).resolve().parents[1]
def render():
 rows={};raw=(ROOT/'machine/z215.tm').read_text()
 assert raw.splitlines()[0]=='#! start 0'
 for line in raw.splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,z=line.split();rows[int(q),int(b)]=(w,d,int(z))
 assert set(rows)=={(q,b) for q in range(215) for b in (0,1)}
 def entry(q,b):
  w,d,z=rows[q,b];return r'\texttt{'+w+d+('H' if z==215 else str(z))+'}'
 out=[r'\begingroup\small',r'\begin{longtable}{rll@{\hspace{2em}}rll}',r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule',r'\endfirsthead',r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule',r'\endhead',r'\midrule\multicolumn{6}{r}{\emph{continued on next page}}\\\endfoot',r'\bottomrule\endlastfoot']
 for q in range(108):
  cells=[str(q),entry(q,0),entry(q,1)];z=q+108
  cells+=([str(z),entry(z,0),entry(z,1)] if z<215 else ['','',''])
  out.append(' & '.join(cells)+r'\\')
 return '\n'.join(out+[r'\end{longtable}',r'\endgroup'])+'\n'
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'machine_table.tex');a=p.parse_args();a.output.write_text(render())
