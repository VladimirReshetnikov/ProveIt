from pathlib import Path
import argparse,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
a=argparse.ArgumentParser();a.add_argument('--output',type=Path,required=True);o=a.parse_args().output;o.mkdir(parents=True,exist_ok=False)
for n in ['zero_terminal','retagged','composed']:
 cmd=[sys.executable,'-B',str(ROOT/'code/check_joint_fold.py'),'--old',str(ROOT/'machine'/n/'k219.native.tm'),'--new',str(ROOT/'machine'/(n+'-row157')/'table.native.tm'),'--radius','7','--fuel','97','--output',str(o/(n+'.json'))]
 with(o/(n+'.log')).open('w')as log:subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=120,check=True)
print('THREE_ROW157_JOINT_CHECKS_PASS')
