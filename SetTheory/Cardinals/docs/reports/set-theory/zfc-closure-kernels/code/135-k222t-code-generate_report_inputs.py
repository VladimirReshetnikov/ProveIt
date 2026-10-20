#!/usr/bin/env python3
"""Generate exact readable transition tables and TeX metrics from package data."""
from pathlib import Path
import argparse,hashlib,json
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);a=ap.parse_args()
 root=a.root.resolve();macros=[]
 for variant,prefix in(('conditional','Cond'),('seed','Seed')):
  raw=(root/'machines'/variant/'candidate222.tm').read_bytes()
  table={}
  for line in raw.decode('ascii').splitlines():
   if not line or line.startswith('#'):continue
   q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));table[q,b]=(w,d,z)
  assert set(table)=={(q,b)for q in range(222)for b in(0,1)}
  receipt=json.loads((root/'evidence'/variant/'runtime.json').read_text())
  sites=json.loads((root/'machines'/variant/'sites.json').read_text())
  values={'Cases':f"{receipt['cases']:,}",'Rules':f"{receipt['symbolic_steps']:,}",
   'Depth':str(max(len(s[0])for s in sites)),'Hash':hashlib.sha256(raw).hexdigest()}
  for name,value in values.items():macros.append('\\newcommand{\\'+prefix+name+'}{'+value+'}')
  lines=['\\begingroup\\small\\setlength{\\tabcolsep}{6pt}',
   '\\begin{longtable}{rll@{\\hspace{1.1em}}rll@{\\hspace{1.1em}}rll}',
   '\\toprule',
   'State & 0 & 1 & State & 0 & 1 & State & 0 & 1 \\\\',
   '\\midrule\\endfirsthead',
   '\\toprule State & 0 & 1 & State & 0 & 1 & State & 0 & 1 \\\\',
   '\\midrule\\endhead',
   '\\midrule\\multicolumn{9}{r}{\\small Continued on next page}\\\\\\endfoot',
   '\\bottomrule\\endlastfoot']
  for row in range(74):
   fields=[]
   for column in range(3):
    q=row+74*column;fields.append(str(q))
    for bit in(0,1):
     w,d,z=table[q,bit];fields.append(f'${w}{d}'+('H'if z==222 else str(z))+'$')
   lines.append(' & '.join(fields)+' \\\\')
  lines+=['\\end{longtable}','\\endgroup']
  (root/'report'/('table_'+variant+'.tex')).write_text('\n'.join(lines)+'\n')
 (root/'report/metrics.tex').write_text('\n'.join(macros)+'\n')
 print('Report tables and metrics generated from both literal tables and checked receipts.')
if __name__=='__main__':main()
