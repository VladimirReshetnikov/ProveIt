#!/usr/bin/env python3
"""Reproduce all delivered finite audits, including the inherited source chain."""
import argparse,json,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parent
flags=['-B']+(['-O'] if sys.flags.optimize else [])
def run(path,*args):
 p=subprocess.run([sys.executable,*flags,str(path),*map(str,args)],capture_output=True,text=True,cwd=R)
 if p.returncode:raise ValueError(p.stdout+'\n'+p.stderr)
 return json.loads(p.stdout)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);ap.add_argument('--skip-parent-rebuild',action='store_true');a=ap.parse_args()
 if (R/'sources/common_remainders252.json').read_bytes()!=(R/'source_closure/common_remainders/equation/equation.json').read_bytes():raise ValueError('source copy differs from independently rebuilt parent')
 result={'status':'pass','optimized_python':bool(sys.flags.optimize),'parent_common_source':run(R/'source_closure/common_remainders/code/verify.py',*([] if a.skip_parent_rebuild else ['--rebuild'])),'odd_source_rebuild':run(R/'build_source.py','--check'),'odd_source_independent_audit':run(R/'check_source.py'),'endpoints':run(R/'check.py','--rebuild'),'readable_transcription_and_maps':run(R/'export_readable.py','--check'),'affine_multiplier_obstruction':run(R/'macaulay_rank.py','--controls')}
 txt=json.dumps(result,indent=2)+'\n'
 if a.output:a.output.write_text(txt)
 print(txt,end='')
