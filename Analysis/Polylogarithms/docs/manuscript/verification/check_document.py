"""Static manuscript integrity and source-coverage checks."""
from pathlib import Path
from collections import Counter
import hashlib, json, re
B=Path(__file__).resolve().parents[1]
files=[B/'polylogarithms.tex',B/'references.tex',*sorted((B/'chapters').glob('*.tex'))]
text='\n'.join(p.read_text(encoding='utf-8') for p in files)
labels=re.findall(r'\\label\{([^}]+)\}',text)
refs=re.findall(r'\\(?:eqref|ref|autoref)\{([^}]+)\}',text)
bibkeys=re.findall(r'\\bibitem\{([^}]+)\}',text)
cites=[k.strip() for group in re.findall(r'\\cite\{([^}]+)\}',text) for k in group.split(',')]
inventory=json.loads((B/'source-inventory.json').read_text(encoding='utf-8'))
changed=[row['path'] for row in inventory if hashlib.sha256((B.parent/row['path']).read_bytes()).hexdigest()!=row['sha256']]
ledger=(B/'EDITORIAL-LEDGER.md').read_text(encoding='utf-8')
uncovered=[row['path'] for row in inventory if Path(row['path']).stem.split('__')[0] not in ledger]
missing_inputs=[m for m in re.findall(r'\\input\{([^}]+)\}',text) if not (B/(m+'.tex')).exists()]
result=dict(source_documents=len(inventory),changed_source_digests=changed,uncovered_sources=uncovered,
 duplicate_labels=[k for k,n in Counter(labels).items() if n>1],missing_references=sorted(set(refs)-set(labels)),
 duplicate_bibliography_keys=[k for k,n in Counter(bibkeys).items() if n>1],missing_citations=sorted(set(cites)-set(bibkeys)),
 missing_inputs=missing_inputs,source_files=len(files),source_bytes=sum(p.stat().st_size for p in files))
result['passed']=not any(v for k,v in result.items() if isinstance(v,list))
(B/'verification/document-integrity.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
raise SystemExit(0 if result['passed'] else 1)
