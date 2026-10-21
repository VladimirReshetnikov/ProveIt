#!/usr/bin/env python3
"""Make a portable selected plan for a recovered Source157 package; no replay."""
from pathlib import Path
import argparse,hashlib,json
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--package',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 here=Path(__file__).resolve().parent;original=here/'replay-plan.json';plan=json.loads(original.read_text());package=a.package.resolve()
 assert package.is_dir()and not a.output.exists()
 for r in plan['inspected_closure']+plan['selected_data']:
  assert sha(package/r['path'])==r['sha256'],r['path']
 plan['package']=str(package)
 for j in plan['jobs']:j['package']=str(package)
 plan['adapter']['original']['path']=str(package/'source-layout/verify_sources.py')
 plan['adapter']['successor']['path']=str(here/'verify_sources_intake.py')
 assert sha(here/'verify_sources_intake.py')==plan['adapter']['successor']['sha256']
 plan['prepared_from']=dict(plan_sha256=sha(original),preparer_sha256=sha(__file__),scope='Only package paths rebound; selected code/data identities, adapter and semantic gates unchanged.')
 a.output.write_text(json.dumps(plan,indent=2)+'\n');print(a.output)
if __name__=='__main__':main()
