#!/usr/bin/env python3
"""Compare a complete numeric binary TM against the pinned current corpus.

Exact canonical action graphs allow state renaming, any graph-spanning root,
reflection, and global bit exchange. A mismatch is a structural novelty check,
not a proof of semantic inequivalence or correctness.
"""
from pathlib import Path
import argparse,hashlib,json
from inventory_census import parse_table,canonical

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('candidate',type=Path)
 ap.add_argument('--census',type=Path,default=Path(__file__).resolve().parent/'current_census/census.json')
 ap.add_argument('--output',type=Path)
 args=ap.parse_args()
 b=args.candidate.read_bytes();data=parse_table(b)
 if data is None:raise SystemExit('Candidate is outside the complete numeric binary-table grammar.')
 forms=[c for r,k in [(False,False),(True,False),(False,True),(True,True)]for q in sorted(data[1])if(c:=canonical(data,q,r,k))is not None]
 if not forms:raise SystemExit('Candidate has no graph-spanning working-state root.')
 h=hashlib.sha256(repr(min(forms)).encode()).hexdigest()
 census=json.loads(args.census.read_text())
 matches=[x for x in census['identities']if x['states']==len(data[1])and x['cosmetic_hash']==h]
 refs=[x for x in census['occurrences']if x['sha256']in {m['sha256']for m in matches}]
 result=dict(candidate_sha256=hashlib.sha256(b).hexdigest(),states=len(data[1]),snapshot=census['snapshot'],cosmetic_hash=h,existing_byte_forms=matches,existing_occurrences=refs,novel_up_to_renaming_root_reflection_and_complement=not bool(matches),scope=__doc__)
 s=json.dumps(result,indent=2)+'\n'
 if args.output:args.output.write_text(s)
 print(s)
if __name__=='__main__':main()
