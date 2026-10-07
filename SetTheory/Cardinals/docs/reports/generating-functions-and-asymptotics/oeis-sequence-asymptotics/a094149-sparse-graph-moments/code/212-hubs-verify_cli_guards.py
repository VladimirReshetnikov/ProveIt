#!/usr/bin/env python3
"""Probe generator argument/output failures and replay destination safeguards."""
import argparse
import json
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
ROOT = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--binary',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args = parser.parse_args()
binary = args.binary.resolve()
results = []


def rejected(command,marker,cwd,case,preexec_fn=None):
    result = subprocess.run([str(x) for x in command],cwd=cwd,text=True,capture_output=True,
                            check=False,preexec_fn=preexec_fn)
    if result.returncode == 0 or marker not in result.stderr:
        raise RuntimeError({'case':case,'expected_marker':marker,'returncode':result.returncode,
                            'stderr':result.stderr})
    results.append({'case':case,'nonzero_exit':True,'intended_failure_marker':True})


with tempfile.TemporaryDirectory(prefix='report212-cli-') as temporary:
    temp = Path(temporary)
    for label,arguments in (('missing',[]),('extra',['2','3']),('zero',['0']),('negative',['-1']),
                            ('nonnumeric',['abc']),('trailing',['3x']),('too_large',['513']),
                            ('overflow',['999999999999999999999999'])):
        rejected([binary]+arguments,'GENERATOR_FAILED[argument]',temp,label)
    for filename in ('moments_exact.tsv','root_counts_exact.tsv'):
        folder = temp/filename.replace('.','_')
        folder.mkdir()
        (folder/filename).mkdir()
        rejected([binary,'2'],'GENERATOR_FAILED[open]',folder,'open_'+filename)
    # On the documented Unix/GMP build platform, a zero file-size limit forces
    # an actual flush/write failure. Ignoring SIGXFSZ lets iostream report EFBIG.
    import resource
    def block_file_writes():
        resource.setrlimit(resource.RLIMIT_FSIZE,(0,0))
        signal.signal(signal.SIGXFSZ,signal.SIG_IGN)
    folder = temp/'write_failure'
    folder.mkdir()
    rejected([binary,'2'],'GENERATOR_FAILED[write]',folder,'write_failure',block_file_writes)
    # Destination checks must fail before creating/overwriting anything.
    existing = temp/'existing'
    existing.mkdir()
    for label,destination,marker in (
            ('existing_work',existing,'work_directory_new'),
            ('source_root',ROOT,'work_directory_scope'),
            ('source_ancestor',ROOT.parent,'work_directory_scope'),
            ('source_code_child',ROOT/'code'/'must_not_be_created','work_directory_scope')):
        rejected([sys.executable]+(['-O'] if sys.flags.optimize else [])+
                 [ROOT/'code'/'reproduce.py','quick','--work-dir',destination],
                 f'CHECK_FAILED[{marker}]',temp,label)
    if list(existing.iterdir()) or (ROOT/'code'/'must_not_be_created').exists():
        raise RuntimeError('CHECK_FAILED[destination_no_writes]')
    # One successful tiny generation makes the failure probes non-vacuous.
    success = temp/'tiny_generation'
    success.mkdir()
    subprocess.run([str(binary),'2'],cwd=success,check=True,capture_output=True,text=True)
    if ((success/'moments_exact.tsv').read_text() != 'k\tM2k\n0\t1\n1\t1\n2\t3\n' or
        (success/'root_counts_exact.tsv').read_text() != 'k\tm\tcount\n1\t1\t1\n2\t1\t1\n2\t2\t2\n'):
        raise RuntimeError('CHECK_FAILED[tiny_generator_output]')
report = {'all_checks_passed':True,'failure_tests_passed':len(results),
          'tiny_generation_k2_passed':True,'invalid_destinations_unmodified':True,
          'scope':'C++ bad-argument/open/write guards and Python replay destination guards.',
          'tests':results}
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'all_checks_passed':True,'failure_tests_passed':len(results)},indent=2))
