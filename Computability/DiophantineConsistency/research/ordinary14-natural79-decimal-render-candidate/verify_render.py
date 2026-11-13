#!/usr/bin/env python3
"""Check candidate PDF extraction only; does not generate or invoke Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent
tex=(P/'equation.tex').read_bytes();pdf=(P/'equation.pdf').read_bytes();meta=json.loads((P/'result.json').read_bytes())
assert hashlib.sha256(tex).hexdigest()==meta['tex_sha256']
info=subprocess.run(['pdfinfo',str(P/'equation.pdf')],check=True,capture_output=True,text=True).stdout
assert re.search(r'^Pages:\s+4\s*$',info,re.M)
text=subprocess.run(['pdftotext','-raw',str(P/'equation.pdf'),'-'],check=True,capture_output=True,text=True).stdout
section=text.split('Complete decimal integer P.',1)[1].split('This is an unelaborated',1)[0]
chunks=[l.strip() for l in section.splitlines() if re.fullmatch('[0-9]{1,75}',l.strip())]
seed=''.join(chunks);expected=(P/'DECIMAL_SEED.txt').read_text().strip()
assert seed==expected and len(seed)==meta['decimal_seed_digits'] and hashlib.sha256(seed.encode()).hexdigest()==meta['decimal_seed_sha256']
assert 'Overfull' not in (P/'equation.log').read_text()
assert 'source-only candidate' in text and 'not a claim' in text
print(json.dumps({'scope':'point-in-time PDF text seed extraction and no-overfull log observation only; not formal page semantics', 'pages':4,'seed_digit_count':len(seed),'seed_extraction_exact':True,'tex_sha256':hashlib.sha256(tex).hexdigest(),'pdf_sha256':hashlib.sha256(pdf).hexdigest()},sort_keys=True,indent=2))
