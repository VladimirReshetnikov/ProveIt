"""Owned read-only retrieval of pinned proof text and receipts. No fetched code executes."""
from pathlib import Path
import urllib.request,json,hashlib
D=Path(__file__).parent/'reference';D.mkdir(exist_ok=True)
SHA='6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95'
BASE='Computability/BusyBeaver/'
proposal=BASE+'Research/ZFC/k225-formal/verification/k215/simplification/proposals/shared-invariants/decoder-residual/'
paths={
 'residual_README.md':proposal+'README.md',
 'residual_validation-receipt.json':proposal+'evidence/validation-receipt.json',
 'residual_final-recheck.json':proposal+'evidence/receipt-final-recheck.json',
 'KResidualSites215.lean':proposal+'lean/BusyBeaver/ZFC/KResidualSites215.lean',
 'KResidualRouting215.lean':proposal+'lean/BusyBeaver/ZFC/KResidualRouting215.lean',
 'KResidualFast215.lean':proposal+'lean/BusyBeaver/ZFC/KResidualFast215.lean',
}
for n in ('KRuntimeCore.lean','KHome.lean','KHomeReady.lean','KSim.lean','KEndpoint.lean','KDecoderPrefix215.lean','KTable215.lean','K215Decoder.lean'):
 paths[n]=BASE+'Lean/BusyBeaver/ZFC/'+n
pins={}
for n,path in paths.items():
 url='https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/'+SHA+'/'+path
 data=urllib.request.urlopen(url).read();(D/n).write_bytes(data)
 pins[n]=dict(url=url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));print(n,len(data))
(D/'PINS.json').write_text(json.dumps(pins,indent=2))
