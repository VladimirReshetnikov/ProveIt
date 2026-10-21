from pathlib import Path
import ast,json,hashlib,sys
D=Path(__file__).parent;R=D.parents[1]
src=D/'inputs/KDense215.lean';s=src.read_text()
raw=s.split('def rows215')[1].split(':=',1)[1].split('\ndef act')[0].strip();rows=ast.literal_eval(raw.replace('true','True').replace('false','False'))
labels=ast.literal_eval(s.split('def denseLabels')[1].split(':=',1)[1].split('\ndef expand')[0].strip());assert len(rows)==len(labels)==215
from check_decoder import table
p=D/'inputs/K215_Formal.tm';T=table(p);M={q:q for q,b in T};M.update({301:102,302:120,254:230});assert len(set(M[q]for q,b in T))==215
F={(labels[i],b):(int(w),1 if d else-1,labels[z]if z<215 else 230)for i,row in enumerate(rows)for b,(w,d,z)in enumerate(row)}
assert F=={(M[q],b):(w,d,M[z])for(q,b),(w,d,z)in T.items()}
out=dict(status='ALL_430_ROWS_EXACTLY_RELABEL',native_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),formal_dense_file_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),nonidentity_native_to_formal={q:z for q,z in M.items()if q!=z},start_native=0,start_formal=0,scope='Parsed literal KDense215.rows215 and denseLabels; inspected KDense215.commutes is the existing formal bridge to tm215. No new compiler run claimed.')
(D/'FORMAL_ALIGNMENT.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
