#!/usr/bin/env python3
"""Replay exact construction and literal physical certificates in temporary files."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile,time
HERE=Path(__file__).resolve().parent
EXPECTED={'machine':'c5787c6f2350e77183ca0d3ff25d2733ba87e8bb52cd54092d7fa26fcf4d5253','baseline':'4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f'}
def run(root,quick):
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must remain enabled.')
    started=time.monotonic()
    for family,script in [('machine','build_4l.py'),('baseline','build_baseline.py')]:
        dest=root/family
        subprocess.run([sys.executable,'-B',str(HERE/'construction'/script),'--output',str(dest)],check=True)
        for f in ['machine.tm','machine.native.tm','labels.json','sites.json','instructions.json']:
            if (HERE/family/f).exists():
                assert (dest/f).read_bytes()==(HERE/family/f).read_bytes(),(family,f)
        assert hashlib.sha256((dest/'machine.tm').read_bytes()).hexdigest()==EXPECTED[family]
        if not quick:
            subprocess.run([sys.executable,'-B',str(HERE/'verification'/'check.py'),str(dest)],check=True)
            assert json.loads((dest/'independent'/'receipt.json').read_text())['status']=='PASS'
    assert (root/'machine'/'instructions.json').read_bytes()==(root/'baseline'/'instructions.json').read_bytes()
    receipt={'status':'PASS','mode':'construction_only'if quick else'full','new_table_sha256':EXPECTED['machine'],'baseline_table_sha256':EXPECTED['baseline'],'resolved_sources_identical':True,'independent_literal_checks_rerun':not quick,'elapsed_seconds':round(time.monotonic()-started,3),'scope':'Exact implementations and source correspondence; no new PA-consistency calibration or proof-assistant endpoint.'}
    (root/'replay_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--quick',action='store_true',help='Skip both independent literal-row passes and report that omission.');p.add_argument('--work',type=Path,help='Use a new or empty directory and retain regenerated evidence.')
    a=p.parse_args()
    if a.work:
        dest=a.work.resolve();dest.mkdir(parents=True,exist_ok=True)
        if any(dest.iterdir()):raise ValueError('--work must be a new or empty directory')
        run(dest,a.quick)
    else:
        with tempfile.TemporaryDirectory(prefix='pa194_4l_replay_')as d:run(Path(d),a.quick)
if __name__=='__main__':main()
