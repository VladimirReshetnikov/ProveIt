"""Restore three generated historical names in a separate, unintegrated draft."""
from pathlib import Path
import hashlib,json,os
P=Path('/tmp/adaptive-wang-table-split-src'); Q=Path(os.environ.get('WANG_TABLE_COMPAT_SRC','/tmp/adaptive-wang-table-compat-src')); gen=json.loads((P/'generation.json').read_text()); src=P/'DiophantineConsistency/ArithmeticWangTable.lean'; raw=src.read_bytes(); sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(raw)==gen['draft_sha256'] and sha(Path(gen['original']).read_bytes())==gen['original_sha256']
s=raw.decode();marker='theorem tileN_mem';assert s.count(marker)==1
added=''.join(f'theorem rows_good{k}._proof_1 : ∀ row ∈ orderedRows, Good{k} row.2 := rows_good{k}\n' for k in 'ABC')+'\n'
draft=s.replace(marker,added+marker,1);out=Q/'DiophantineConsistency';out.mkdir(parents=True,exist_ok=True);(out/'ArithmeticWangTable.lean').write_text(draft)
(Q/'generation.json').write_text(json.dumps({'original':gen['original'],'original_sha256':gen['original_sha256'],'draft_sha256':sha(draft.encode()),'parent_draft_sha256':gen['draft_sha256'],'insertion':added,'scope':'uncompiled private compatibility draft; restores three generated historical names; no full interface or provider compatibility claim'},indent=2)+'\n');(Q/'original-snapshot.lean').write_bytes(Path(gen['original']).read_bytes())
