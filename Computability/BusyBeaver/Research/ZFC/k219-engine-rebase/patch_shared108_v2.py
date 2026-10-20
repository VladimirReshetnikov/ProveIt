#!/usr/bin/env python3
"""Retarget only P=(CD6,CC2) decoder children to explicit shared108 entry.

Preserves arithmetic entry13 including its original q8/1 caller; changes108/1 to the exact K219 row. This is
an explicitly unverified contextual-entry hypothesis until runtime succeeds.
"""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True;sys.path.insert(0,str(HERE/'code'))
import source_language as s,build221 as b
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 import argparse
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 assert __debug__ and not a.out.exists();a.out.mkdir(parents=True)
 P=(('CD',6),('CC',2));records=[]
 for hit in (0,1,2,3,12):
  p=a.run/'native220'/f'hit{hit:02}-origins-entry-hypothesis.tm';rec=json.loads(p.with_suffix('.json').read_text());assert sha(p)==rec['raw_sha256']
  sp=HERE.parent/f'k219-source-search/candidates/hit{hit:02}.sites.json';assert sha(sp)==rec['source_sha256']
  tree=s.tree(json.loads(sp.read_text()));old=b.read_table(p.read_bytes());g,paths=b.decoder_map(old,tree);new=dict(old);edits=[]
  assert old[108,0]==(0,1,21) and old[108,1]==(0,-1,40)
  for q,nodes in g.items():
   for n in nodes:
    for bit,child in enumerate(n):
     if child==P and q!=8:
      assert old[q,bit]==(bit,1,13),(q,bit,old[q,bit])
      new[q,bit]=(bit,1,108);edits.append([q,bit,list(old[q,bit]),list(new[q,bit])])
  assert edits;new[108,1]=(0,-1,10);edits.append([108,1,list(old[108,1]),list(new[108,1])])
  ng,np=b.decoder_map(new,tree)
  oldrel={n:{q for q,ns in g.items() if n in ns} for ns in g.values() for n in ns}
  newrel={n:{q for q,ns in ng.items() if n in ns} for ns in ng.values() for n in ns}
  assert set(oldrel)==set(newrel)
  assert all(newrel[n]==({13,108} if n==P else oldrel[n]) for n in oldrel)
  raw=b.table_bytes(new);b.read_table(raw);target=a.out/f'hit{hit:02}.native.tm';target.write_bytes(raw)
  records.append(dict(hit=hit,old_path=str(p.resolve()),old_sha256=sha(p),source_path=str(sp.resolve()),source_sha256=sha(sp),new_path=str(target.resolve()),new_sha256=sha(target),states=len(new)//2,edits=edits,P_paths_before={q:paths[q] for q in oldrel[P]},P_paths_after={q:np[q] for q in newrel[P]}))
 (a.out/'result.json').write_text(json.dumps(dict(status='EXACT_DECODER_RELATION_PATCHED_RUNTIME_PENDING',records=records,scope=__doc__.strip()),indent=2)+'\n')
 print([(x['hit'],x['states'],len(x['edits'])) for x in records])
if __name__=='__main__':main()
