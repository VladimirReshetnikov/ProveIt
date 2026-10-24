#!/usr/bin/env python3
"""Compare complete literal TeX proof transcripts with their authoritative prose."""
import re,json,hashlib
from pathlib import Path
R=Path(__file__).resolve().parents[1]
MAP=[('scalar/PROOF.md','scalar_full.tex'),('norm/DEGREE_PROOF.md','norm_full.tex'),('scalar/CRT_CARRIER_PROOF.md','crt_full.tex'),('norm_weak/DEGREE_PROOF.md','weak_degree_full.tex'),('architecture/UNIFIED_PRODUCT_PROOF.md','architecture_full.tex'),('direct/PROOF.md','direct_full.tex')]
def compact(s):return re.sub(r'\s+','',s)
def md(s):
 s=s.replace('−','-').replace('≠','!=').replace('constant81','constant 81')
 s=re.sub(r'^(?:\d+\.|-)\s+','',s,flags=re.M)
 s=re.sub(r'^#{1,4}\s+','',s,flags=re.M)
 return compact(s.replace('`',''))
def tex(s):
 s=re.sub(r'^%.*$','',s,flags=re.M)
 s=s.replace(r'\allowbreak{}','')
 for a,b in [(r'\textbackslash{}','\\'),(r'\textasciicircum{}','^'),(r'\textasciitilde{}','~'),(r'\textless{}','<'),(r'\textgreater{}','>'),(r'\textasteriskcentered{}','*')]:s=s.replace(a,b)
 s=re.sub(r'\\(?:section|subsection\*|subsubsection\*|paragraph|texttt)\{([^{}]*)\}',r'\1',s)
 s=re.sub(r'\\(?:begin|end)\{(?:verbatim|enumerate|itemize)\}','',s)
 s=s.replace(r'\item ','')
 for c in r'{}$&#%_':s=s.replace('\\'+c,c)
 return compact(s)
result=[]
for src,dst in MAP:
 sp=R/src;tp=R/'report'/dst;a=md(sp.read_text());b=tex(tp.read_text());ok=a==b
 row={'proof':src,'tex':f'report/{dst}','source_sha256':hashlib.sha256(sp.read_bytes()).hexdigest(),'tex_sha256':hashlib.sha256(tp.read_bytes()).hexdigest(),'normalized_proof_characters':len(a),'exact_normalized_transcript':ok}
 if not ok:
  i=next((i for i,(x,y) in enumerate(zip(a,b)) if x!=y),min(len(a),len(b)));row['difference_offset']=i;row['source_context']=a[max(0,i-70):i+150];row['tex_context']=b[max(0,i-70):i+150]
 result.append(row)
print(json.dumps(result,indent=2))
(R/'report_audit/PROOF_COVERAGE.json').write_text(json.dumps(result,indent=2)+'\n')
if not all(x['exact_normalized_transcript'] for x in result):
    raise SystemExit('At least one complete proof transcript differs from its authoritative source.')
