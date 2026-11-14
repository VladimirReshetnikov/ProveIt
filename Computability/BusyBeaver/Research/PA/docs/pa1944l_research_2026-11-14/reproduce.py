#!/usr/bin/env python3
"""Reconstruct and verify the delivered research artifacts without network access.

Default: both complete literal-tape replays. --quick omits those two replays
and explicitly reports the omission; it still reconstructs both tables and
rechecks source identity, startup, folded contracts, novelty, and Boolean data.
Neither mode claims a new PA-consistency calibration or proof-assistant build.
"""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,tempfile,time

ROOT=Path(__file__).resolve().parent

def checked(argv,**kw):
    return subprocess.run([sys.executable,'-B',*map(str,argv)],check=True,**kw)

def main():
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Run with assertions enabled, without Python -O.')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--quick',action='store_true')
    p.add_argument('--receipt',type=Path)
    a=p.parse_args();start=time.monotonic()
    manifest=ROOT/'SHA256SUMS'
    if manifest.exists():
        for ln in manifest.read_text().splitlines():
            expected,path=ln.split('  ',1)
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected,path
    with tempfile.TemporaryDirectory(prefix='pa1944l_research_replay_') as d:
        tmp=Path(d)
        cmd=[ROOT/'replay_physical.py','--work',tmp/'physical']
        if a.quick:cmd.append('--quick')
        checked(cmd)
        physical=json.loads((tmp/'physical/replay_receipt.json').read_text())
        # This checker writes its receipt beside itself; isolate that write.
        theory=tmp/'theory';theory.mkdir()
        shutil.copy2(ROOT/'theory/check_boolean_obstruction.py',theory)
        checked([theory/'check_boolean_obstruction.py'])
        assert (theory/'boolean_obstruction_receipt.json').read_bytes()==(ROOT/'theory/boolean_obstruction_receipt.json').read_bytes()
        clock=checked([ROOT/'theory/summarize_durations.py',ROOT/'machine/independent/contracts.json'],capture_output=True,text=True)
        duration=json.loads(clock.stdout)
        assert duration==json.loads((ROOT/'theory/physical_duration_bounds.json').read_text())
        checked([ROOT/'comparison/compare_novelty.py',ROOT/'machine/machine.tm',ROOT/'comparison/census/frontier_tables','--output',tmp/'novelty.json'])
        novelty=json.loads((tmp/'novelty.json').read_text())
        assert novelty['compared_classes']==82 and novelty['matches']==[]
        for family in ('machine','baseline'):
            record=json.loads((ROOT/family/'independent/receipt.json').read_text())
            assert record['status']=='PASS' and record['source_outcomes']==4780
            assert record['contracts_sha256']==hashlib.sha256((ROOT/family/'independent/contracts.json').read_bytes()).hexdigest()
            assert record['dense_sha256']==hashlib.sha256((ROOT/family/'machine.tm').read_bytes()).hexdigest()
        result={'status':'PASS','mode':'assembly_quick' if a.quick else 'full',
                'physical':physical,'boolean_receipt_reproduced':True,
                'affine_duration_bound_reproduced':True,
                'prior_194_graph_classes_compared':82,'novelty_matches':[],
                'recorded_full_independent_receipts_bound_to_exact_tables':True,
                'absolute_ipra_con_pa_equivalence_established':False,
                'new_proof_assistant_build_performed':False,
                'elapsed_seconds':round(time.monotonic()-start,3)}
        if a.receipt:
            a.receipt.resolve().parent.mkdir(parents=True,exist_ok=True)
            a.receipt.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
