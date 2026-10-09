"""Run self-contained tests; retain machine-readable counts and a text log."""
import argparse,datetime,importlib.util,json,platform,sys,time,unittest
from pathlib import Path
BASE=Path(__file__).resolve().parents[1]
def main():
    p=argparse.ArgumentParser();p.add_argument('--output',default=str(BASE/'data'/'test_summary.json'));args=p.parse_args()
    spec=importlib.util.spec_from_file_location('research_tests',BASE/'tests'/'test_research.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    out=Path(args.output);out.parent.mkdir(parents=True,exist_ok=True);start=time.perf_counter()
    with out.with_suffix('.txt').open('w') as log: r=unittest.TextTestRunner(stream=log,verbosity=2).run(unittest.defaultTestLoader.loadTestsFromModule(m))
    payload={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'python':sys.version,'platform':platform.platform(),'seconds':time.perf_counter()-start,'tests':r.testsRun,'failures':len(r.failures),'errors':len(r.errors),'skipped':len(r.skipped),'counts':m.COUNTS}
    out.write_text(json.dumps(payload,indent=2)+'\n');print(json.dumps(payload,indent=2));print(out.with_suffix('.txt').read_text())
    return 0 if r.wasSuccessful() else 1
if __name__=='__main__': raise SystemExit(main())
