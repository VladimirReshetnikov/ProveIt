"""Fail-closed quick validation, with preserved optimization level and read-only inputs."""
from pathlib import Path
import subprocess,sys,json
from repair_common import options

def main():
    args=options('Repaired quick validation of the original complete certificate data')
    root=Path(__file__).resolve().parent
    summary={'all_checks_passed':False,'completed_scripts':[],'optimization':sys.flags.optimize}
    # Python -O is not automatically inherited through sys.executable alone.
    flags=['-'+'O'*sys.flags.optimize] if sys.flags.optimize else []
    try:
        for name in ['verify_cutoff.py','check_trace_coverage.py','check_m2_response.py','check_m2_pressure.py']:
            subprocess.run([sys.executable,*flags,str(root/name),'--data-dir',str(args.data_dir),'--output-dir',str(args.output_dir)],check=True)
            summary['completed_scripts'].append(name)
        summary['all_checks_passed']=True
    except Exception as exc:
        summary['error']=f'{type(exc).__name__}: {exc}'
        (args.output_dir/'run_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
        print('Quick validation FAILED; no complete certificate claim',file=sys.stderr)
        return 1
    (args.output_dir/'run_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('All four repaired quick checks passed, including all 68 traces; no matrix regeneration was performed')
    return 0

if __name__=='__main__':raise SystemExit(main())
