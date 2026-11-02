#!/usr/bin/env python3
"""Run original endpoint audit with only its plan-audit path rebound to a historical view."""
import argparse,hashlib,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];ORIGINAL=ROOT/'Computability/DiophantineConsistency/reviews/thirteen-model-endpoint-successor-pair-independent-audit/audit.py';H='ec4892d88e69a9f53d3d93d48ce9e43cc8a5f9631ed4a885af17a40011858681';SOURCE='Computability/DiophantineConsistency/Lean/DiophantineConsistency/ModelCarrierCurrent.lean';OLD='3f76453da57164d06bd338928d0e3d587df46851c77d5cbc4fbf858119719076'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--historical-view',type=Path,required=True);view=ap.parse_args().historical_view.resolve()
 if view.parent!=Path('/tmp').resolve() or not view.name.startswith('ipra-historical-audit-review-'):raise ValueError('invalid historical view')
 if sha(ORIGINAL)!=H or sha(view/SOURCE)!=OLD:raise ValueError('original audit or historical source drift')
 plan=view/'Computability/DiophantineConsistency/reviews/thirteen-model-endpoint-closure-independent-audit'
 if sha(plan/'audit.py')!='30ccbcaa1050d3c9e6b9e4b73e930928fd93cba2380bba3ecdb629de755e587c' or sha(plan/'CHECK.json')!='ab2255186de1e61028731a47a1c92e89792835efe7317e4560b86861bc002af7':raise ValueError('historical plan-audit drift')
 sp=importlib.util.spec_from_file_location('unchanged_endpoint_audit',ORIGINAL);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
 m.PARENTAUDIT=plan
 m.main()
if __name__=='__main__':main()
