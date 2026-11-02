import hashlib,json,re
from pathlib import Path
b=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/ordinary12-ipra-bridge');plan=json.loads((b/'compact44-direct-k-band-join-plan/scan.json').read_bytes());H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();out=[]
for row in plan['source_order']:
 name=row['module'].split('.')[-1];src=Path(row['source']);sha=row['source_sha256'];assert H(src)==sha
 if name in ('ArithmeticCyclicWord','ArithmeticWindowCarry'):
  snap=Path('/tmp/ipra-thirteen-current-source-02/src/DiophantineConsistency')/(name+'.lean');assert H(snap)==sha
  receipt=json.loads(Path('/tmp/ipra-thirteen-parent-window-pair-01/receipt.json').read_bytes());runs=[x for x in receipt['runs'] if x['label']=='author' and x['module']==row['module']];assert len(runs)==1 and runs[0]['source_sha256']==sha and runs[0]['exit']==0
  log=Path('/tmp/ipra-thirteen-parent-window-pair-01/author')/('DiophantineConsistency_'+name+'.log');assert H(log)==runs[0]['log_sha256'];kind='matched window source, compiler receipt and log'
 elif name=='CompactCoefficientDecoder':
  r=json.loads((b/'compact44-coefficient-decomposition-pair-prototype/evidence/receipt.json').read_bytes());log=b/'compact44-coefficient-decomposition-pair-prototype/evidence/author/compiler.log';assert r['runs'][0]['compiler_exit']==0 and H(log)==r['runs'][0]['log_sha256'];assert H(src)=='86f9ddd083eb5767359a691774c76c88a5e7c1627dc693f474880a78e32a03c8';kind='matched audited coefficient source pin and compiler receipt'
 elif name=='CompactPartialBand':
  assert H('/tmp/ipra-partial-band-explore/CompactPartialBand.lean')==sha;log=b/'compact44-partial-band-prototype/observation.txt';text=log.read_text();assert 'observed exit 0' in text and "'CompactPartialBand.band_decomposition' depends on axioms:" in text;kind='source-matched exploratory compiler-output transcription'
 elif name=='CompactPartialBandRotation':
  r=json.loads((b/'compact44-partial-band-rotation-prototype/evidence/observation.json').read_bytes());log=b/'compact44-partial-band-rotation-prototype/evidence/compiler.log';assert r['source_sha256']==sha and r['observed_exit']==0 and H(log)==r['compiler_log_sha256'];kind='matched exploratory source hash and compiler log'
 else:
  e=src.parent/'evidence';r=json.loads((e/'receipt.json').read_bytes());run=r['runs'][0];log=e/'author.log';assert run['source_sha256']==sha and run['compiler_exit']==0 and H(log)==run['log_sha256'] and log.read_text()==run['stdout'];kind='matched paired source hash and compiler receipt'
 text=log.read_text();warnings=[]
 if 'warning:' in text:
  assert text.count('warning:')==1 and name in ('ArithmeticCyclicWord','ArithmeticWindowCarry')
  marker=':145:38:' if name=='ArithmeticCyclicWord' else ':162:29:'
  assert marker in text and text.index(marker)<text.index('warning:');warnings=[text[text.index(marker):]]
 out.append({'module':name,'source_sha256':sha,'historical_log':str(log),'historical_log_sha256':H(log),'evidence':kind,'warning_suffixes':warnings})
assert len(out)==14
print(json.dumps({'status':'PASS_HISTORICAL_SOURCE_MATCHED_WARNING_SURVEY','entries':out,'scope':'Historical output comparison only; warnings can vary across provider/compiler conditions and unknown new diagnostics must fail.'},indent=2))
