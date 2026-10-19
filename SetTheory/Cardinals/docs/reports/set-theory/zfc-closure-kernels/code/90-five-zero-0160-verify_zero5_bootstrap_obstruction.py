#!/usr/bin/env python3
"""Exact syntactic obstruction to a zero-five source under bootstrap-lock54.

For a binary node (left,right), leading-zero depth is 1+lead(left).
The five locked left projections below, followed by atom e's own fixed left
edge to a leaf, force six consecutive zeros. Therefore no reassociation in
the inherited grammar family can simultaneously retain those locks, retain
the required source root [172], and have maximum zero run at most five.
This is not a Turing-machine state lower bound and does not rule out direct
blank-start validation after relaxing the sufficient bootstrap locks.
"""
import argparse,hashlib,json
from pathlib import Path

def verify(package):
 package=Path(package)
 semantic=package/'reference/grammar/closed-sequence-grammar-next22.json'
 symbols=package/'reference/grammar/semantic-symbols.json'
 source=json.loads(semantic.read_text());sym=json.loads(symbols.read_text())
 locksfile=package/'inputs/state_reduction/bootstrap-lock54.txt'
 lines=locksfile.read_text().splitlines();assert int(lines[0])==54
 locks={(w,int(b)):t for w,b,t in map(str.split,lines[1:])};assert len(locks)==54
 forced=[('eijkKCqkjGeU','eijkKCqkjGe'),('eijkKCqkjGe','eijkKCqkjG'),('eijkKCqkjG','eijkKC'),('eijkKC','eijk'),('eijk','e')]
 for w,t in forced:assert locks[w,0]==t
 atom=source['atoms'][sym['e']];assert atom['state']==34
 ast=source['ast_dag'];a=atom['ast'];assert ast[a][0]=='N'
 leaf=ast[a][1];assert ast[leaf][0]=='L'
 lookup=(package/'reference/grammar/semantic.txt').read_text().splitlines();n=int(lookup[0].split()[0]);names={int(q):w for k,w,q in map(str.split,lookup[1:n+1])}
 assert names[172]=='eijkKCqkjGeU' and 172 in source['required_entry_roots']
 seq_ast=int(source['sequence_ast_roots']['172']);assert seq_ast==221
 def find(i,p=''):
  if i==seq_ast:return p
  r=ast[i]
  if r[0]=='L':return None
  for b,c in enumerate(r[1:]):
   q=find(c,p+str(b))
   if q is not None:return q
  return None
 source_occurrence=find(source['original_ast']);assert source_occurrence is not None
 return dict(status='PASS_EXACT_SYNTACTIC_OBSTRUCTION',locked_left_projections=[dict(word=w,bit=0,target=t)for w,t in forced],fixed_atom=dict(symbol='e',state=34,ast=a,left_leaf_ast=leaf,left_leaf=ast[leaf][1],leading_zero_depth=1),required_source_root=dict(old_state=172,word=names[172],ast=seq_ast,one_original_ast_occurrence=source_occurrence),forced_leading_zero_depth=6,ruled_out='Maximum source-address zero run <=5 while retaining these five left projections and this source-root occurrence',scope='No TM state lower bound. Relaxed bootstrap, different encodings, restricted reachable-path arguments, and other source transformations remain open.',sha256={str(p.relative_to(package)):hashlib.sha256(p.read_bytes()).hexdigest()for p in (semantic,symbols,locksfile)})
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--package',type=Path,default=Path(__file__).resolve().parent/'reference_data');p.add_argument('--output',type=Path);a=p.parse_args()
 if not __debug__:p.error('Assertions must be enabled')
 result=verify(a.package);txt=json.dumps(result,indent=2)+'\n';print(txt,end='')
 if a.output:a.output.write_text(txt)
