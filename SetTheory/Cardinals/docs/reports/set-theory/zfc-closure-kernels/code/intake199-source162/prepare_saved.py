"""Reconstitute the actual selected-input view; no supplied execution."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 host=Path(__file__).resolve().parents[2];saved=host/'data/intake199-source162';repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip());C=repo/'Computability/BusyBeaver/Research/ZFC/candidate-k216';O=a.output.resolve();O.mkdir(parents=True,exist_ok=False)
 for name in('actual.json','logs','results'):
  src=saved/name;dst=O/name
  if src.is_dir():shutil.copytree(src,dst)
  else:shutil.copyfile(src,dst)
 before=json.loads((O/'actual.json').read_text())['before']
 parents={'parents/parent_table/k216.native.tm':C/'k216.native.tm','parents/parent_source/sites216.json':C/'sites216.json','parents/reference_source/sites216.json':C/'alternatives/permuted/sites216.json'}
 for rel,h in before.items():
  src=a.packet/rel[len('packet/'):]if rel.startswith('packet/')else parents[rel]
  b=src.read_bytes();assert hashlib.sha256(b).hexdigest()==h,rel
  dst=O/'inputs'/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
 print('EXACT_SOURCE162_SAVED_VIEW_PREPARED',len(before))
if __name__=='__main__':main()
