#!/usr/bin/env python3
"""Reproducible scoped text search, including nested ZIPs; never executes inputs.

This is a locator aid, not an exhaustive semantic equivalence procedure.
"""
from pathlib import Path
import argparse,hashlib,io,json,re,zipfile
p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--pin',required=True);a=p.parse_args()
text_ext={'.tex','.md','.txt','.py','.cpp','.hpp','.json','.lean'}
patterns=[r'\bh5[_ -]?(?:a|x)\b',r'witness.{0,100}consequen',r'independent.{0,100}consequen',r'\bh1\b.{0,120}\bh5\b',r'\bh5\b.{0,120}\bh1\b',r'\bh1\b.{0,120}(?:disjunct|peirce|positive)',r'(?:disjunct|positive).{0,120}\bh1\b',r'\(\s*X\s*(?:\\to|→|->)\s*H\s*\)\s*(?:\\to|→|->)\s*H']
rx=re.compile('|'.join(patterns),re.I);seen_text=set();seen_archives=set();hits=[]
def walk(blob,label):
 suffix=Path(label).suffix.lower()
 if suffix=='.zip':
  sha=hashlib.sha256(blob).hexdigest()
  if sha in seen_archives:return
  seen_archives.add(sha)
  with zipfile.ZipFile(io.BytesIO(blob)) as z:
   for n in sorted(z.namelist()):
    if n.endswith('/'):continue
    if Path(n).suffix.lower() in text_ext|{'.zip'}:walk(z.read(n),label+'!'+n)
 elif suffix in text_ext:
  sha=hashlib.sha256(blob).hexdigest()
  if sha in seen_text:return
  seen_text.add(sha);s=blob.decode('utf-8',errors='replace');rows=[]
  for n,line in enumerate(s.splitlines(),1):
   if rx.search(line):rows.append({'line':n,'text':line[:1800]})
  if rows:hits.append({'path':label,'sha256':sha,'matches':rows[:30],'total_matching_lines':len(rows)})
for sub in ['Computability/BusyBeaver/Research/PA','docs/incoming']:
 for f in sorted((a.source/sub).rglob('*')):
  if f.is_file() and f.suffix.lower() in text_ext|{'.zip'}:walk(f.read_bytes(),str(f.relative_to(a.source)))
report={'source_revision':a.pin,'scope':__doc__,'patterns':patterns,'distinct_text_payloads':len(seen_text),'distinct_archives':len(seen_archives),'hit_files':len(hits),'hits':hits}
a.output.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['hits','patterns']},indent=2))
