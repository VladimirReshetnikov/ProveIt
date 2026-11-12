#!/usr/bin/env python3
"""Read-only source coverage and finite graph checks; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/adaptive-aq17-forced105-extraction-draft/AQ17Forced105CutExtraction.lean.src': '3aaac2765bebc24bc0c3e08b5a66b704b97183d1fdb981ccf81288bf8e40bc05', 'research/adaptive-aq17-forced105-extraction-draft/AQ17Forced105Endpoint.lean.src': '7395fb0cd9111653070bf55382627df8ccd66c6f8d41148aab47ff056b1ee613', 'research/adaptive-aq17-forced105-extraction-draft/AQ17Forced105Evaluation.lean.src': '6a20d07dd4bf6b2e8f561663260c783e57185107a772baabbbc3fa3295c7f447', 'research/adaptive-aq17-forced105-extraction-draft/generate_evaluation.py': '375db4540b97d507789fecdb64378441b84a17b876512db220ad11d979c12401', 'research/adaptive-aq17-forced105-extraction-draft/generated.json': '45d75b27330c78ec66391fded92768e327225ad925a2df04c3357e00a709ee29', 'research/adaptive-aq17-forced105-model-draft/AQ17Forced105Arithmetic.lean.src': 'b3057437cfb476170b28114283783bb0bd392a28f1de1ba4a39b6bf264b5e330', 'research/adaptive-aq17-forced105-model-draft/AQ17Forced105ConditionalTransfer.lean.src': 'b77bfbaf3c41ff5d33cfa6a31e797bd4be85af3818ed178aa567b6bf5c526779', 'research/adaptive-aq17-forced105-model-draft/AQ17Forced105Literal.lean.src': 'ca9548bcdc73ae480fafe801ad249e45a447f615b0d9bca8edda0c2b74376958', 'research/adaptive-aq17-forced105-model-draft/AQ17Forced105ResidualZeros.lean.src': '767a0adb800e688506f36c2ab4cd5d55deaf05b4c2716fdb3682e204da578021', 'research/adaptive-aq17-forced105-model-draft/AQ17Forced105Residuals.lean.src': 'd9b5cce48d8f89e6e9ec9823f10ebc4ecc23f5c68ba46218c58ef5da15eeb88b', 'research/adaptive-aq17-forced105-model-draft/check.py': '1a2888be31f3545208cb2a69dcb44c4eb9725d684d4c234ee6868362fa34a125', 'research/adaptive-aq17-forced105-model-draft/receipt.json': 'b76c64faa7845e9a18ca94c7d5182119ca9d2db0eaf2f26d1d7f33fbb1e497e3', 'research/adaptive-aq17-natural-forced105/candidate.json': 'ff131760c176ebd56a593aff49523daf384c03322e2ddaae07f65f8f63bb7bac', 'research/adaptive-aq17-natural-forced105/check.py': '663eac086d19c56af6615b5e92fcdfbc1713bfdbfdc013722c3894be2a647561', 'research/adaptive-aq17-natural-forced105/receipt.json': '322913d757b9cac60fb64b7c446026e0922c2d6f782456b8fe5de1f74fecec84'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet,check,receipt in [('adaptive-aq17-forced105-extraction-draft','generate_evaluation.py','generated.json'),('adaptive-aq17-forced105-model-draft','check.py','receipt.json'),('adaptive-aq17-natural-forced105','check.py','receipt.json')]:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/check)],cwd=D)==(p/receipt).read_bytes(),packet
src={x.name:x.read_text() for x in P.glob('*.lean.src')};assert len(src)==3
for n,s in src.items():assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s),n
e=src['AQ17Forced105Evaluation.lean.src'];c=src['AQ17Forced105CutExtraction.lean.src'];ep=src['AQ17Forced105Endpoint.lean.src']
assert sorted(re.findall(r'^theorem relation(\d\d)',e,re.M))==[f'{i:02}' for i in range(8)]
for n in ['qnat_at_least_four','cut_of_zero','forcingCutExtraction']:
 assert f'theorem {n}' in c,n
assert 'ι (v 13+1)' in c and 'haux -' in c
for n in ['h22','h20','h17','zeroEquivalence','forcingCutExtraction']:
 assert n in ep,n
print(json.dumps({'scope':'bounded source and external graph checks; no Lean','pinned_files':len(pins),'source_files':len(src),'evaluation_relations':8,'forcing_residuals':[0,1,2,3,7],'inherited_obligations_explicit':True,'source_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in sorted(src.items())}},sort_keys=True,indent=2))
