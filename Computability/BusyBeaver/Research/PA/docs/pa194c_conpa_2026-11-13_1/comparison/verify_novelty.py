#!/usr/bin/env python3
"""Check a new194 table against every recognized current194 byte form."""
from pathlib import Path
import json,argparse,hashlib
import compare_graphs as g
P=Path(__file__).resolve().parent

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('candidate',type=Path);ap.add_argument('--out',type=Path);args=ap.parse_args()
 corpus=json.loads((P/'census.json').read_text())
 old=[x for x in corpus['tables'] if x['states']==194]
 hashes=sorted({x['byte_sha256'] for x in old});assert len(hashes)==7
 candidate,cf=g.fingerprints(args.candidate);assert candidate['states']==194
 records=[]
 for h in hashes:
  p=P/'current194'/(h+'.tm');assert hashlib.sha256(p.read_bytes()).hexdigest()==h
  fp,forms=g.fingerprints(p)
  iso=cf['mirror0_complement0']==forms['mirror0_complement0']
  refl=any(cf['mirror0_complement0']==forms[f'mirror{m}_complement0'] for m in [0,1])
  both=any(cf['mirror0_complement0']==f for f in forms.values())
  records.append(dict(sha256=h,locators=[x['locator']for x in old if x['byte_sha256']==h],rootfree_sha256=fp['rootfree_sha256'],same_graph=iso,same_allowing_reflection=refl,same_allowing_reflection_and_bit_exchange=both))
 assert not any(x['same_allowing_reflection_and_bit_exchange'] for x in records),'Candidate is already represented'
 result=dict(status='PASS',revision='768c2be1a8e4d2fcf8aa3443c7b0f084d145734c',candidate=candidate,current194_occurrences=len(old),current194_byte_forms=len(hashes),current194_rootfree_graphs=len({x['rootfree_sha256'] for x in records}),all_current194_tables_covered=True,comparison=records,scope='Exact full graph nonisomorphism, including start-forgetting, L/R reflection and bit exchange; no semantic equivalence or global novelty claim')
 if args.out:args.out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
