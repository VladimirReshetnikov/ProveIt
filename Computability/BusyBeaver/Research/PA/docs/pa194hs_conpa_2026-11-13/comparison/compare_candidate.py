#!/usr/bin/env python3
"""Exact tuple graph novelty check against all stored 194-state byte forms."""
import argparse,json
from pathlib import Path
from audit_census import parse,canonical,digest

def main():
 p=argparse.ArgumentParser();p.add_argument('candidate',type=Path);p.add_argument('--census',type=Path,default=Path(__file__).parent/'current');p.add_argument('--output',type=Path);a=p.parse_args()
 data=a.candidate.read_bytes();m=parse(data)
 if m is None:raise SystemExit('Candidate is not a recognized complete binary table')
 target=canonical(m)
 if target is None:raise SystemExit('Candidate has no graph-spanning root; this checker cannot decide novelty')
 rows=json.loads((a.census/'tables.json').read_text());matches=[];checked=0
 for r in rows:
  if r['states']!=len(m[0]):continue
  q=parse((a.census/'literal_tables'/(r['sha256']+'.tm')).read_bytes());checked+=1
  for ref,comp in ((False,False),(True,False),(False,True),(True,True)):
   if canonical(q,ref,comp)==target:
    matches.append({'sha256':r['sha256'],'reflection':ref,'global_symbol_exchange':comp,'paths':r['paths']});break
 out={'candidate':str(a.candidate),'sha256':digest(data),'states':len(m[0]),'corpus_forms_of_same_size':checked,'exact_tuple_comparison':True,'matches':matches,'novel_under_state_renaming_root_changes_reflection_symbol_exchange':not matches}
 if a.output:a.output.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()
