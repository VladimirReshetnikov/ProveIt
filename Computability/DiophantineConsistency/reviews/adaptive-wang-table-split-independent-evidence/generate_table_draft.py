"""Generate an isolated WangTable module using the chunked predicate facts."""
from pathlib import Path
import hashlib,json,os
root=Path(__file__).resolve().parents[2];src=root/'Lean/DiophantineConsistency/ArithmeticWangTable.lean';base=Path(os.environ.get('WANG_TABLE_DRAFT_SRC','/tmp/adaptive-wang-table-split-src'));out=base/'DiophantineConsistency';raw=src.read_bytes();h=hashlib.sha256(raw).hexdigest()
if h!='8bf620443a3ed74892efba1aeaa6f8c14add5feaff4954dda001a6acf5e36ff2':raise RuntimeError('WangTable source pin changed')
s=raw.decode();start='/-! ## Standard data -/';tail='theorem tileN_mem'
if s.count(start)!=1 or s.count(tail)!=1:raise RuntimeError('unexpected source markers')
head=s[:s.index(start)];needle='import DiophantineConsistency.ArithmeticMachineGraph215\n'
if head.count(needle)!=1:raise RuntimeError('unexpected import marker')
head=head.replace(needle,needle+'import DiophantineConsistency.ArithmeticWangTableChunkFacts\n',1);suffix=s[s.index(tail):];out.mkdir(parents=True,exist_ok=True);draft=head+suffix;(out/'ArithmeticWangTable.lean').write_text(draft);(base/'generation.json').write_text(json.dumps({'original':str(src),'original_sha256':h,'draft_sha256':hashlib.sha256(draft.encode()).hexdigest(),'reused_tail_exact':draft.endswith(suffix),'scope':'uncompiled private WangTable source draft; full exports and provider compatibility not checked'},indent=2)+'\n');(base/'original-snapshot.lean').write_bytes(raw)
