#!/usr/bin/env python3
"""Four-occurrence source transfer-plus-one normalization for pinned K230.

This constructs the source graph and two-row 230-state literal basis only.
Runtime/blank-start calibration and subsequent folds have separate obligations.
"""
from pathlib import Path
from collections import Counter
from functools import cache
import json,hashlib,sys,argparse
import source_tools as b
OLD=((('CD',6),(('CI',5),('CC',2))),('CI',5))
NEW=(('CI',5),(('CD',6),('CC',2)))
MARK=('CLOSED_TRANSFER_PLUS_ONE',6,5)
def replace(n,old,new):
 if n==old:return new
 if isinstance(n[0],str):return n
 return replace(n[0],old,new),replace(n[1],old,new)
def occurrences(n,target,p=''):
 if n==target:return [p]
 if isinstance(n[0],str):return []
 return occurrences(n[0],target,p+'0')+occurrences(n[1],target,p+'1')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def parse(p):
 t={}
 for line in Path(p).read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,c,w,d,z=line.split();t[int(q),int(c)]=(int(w),1 if d=='R' else -1,int(z))
 return t
def encode(t):return ('#! start 0\n'+''.join(f'{q} {c} {w} {"R" if d==1 else "L"} {z}\n' for(q,c),(w,d,z) in sorted(t.items()))).encode()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,required=True,help='Pinned k230-rocq repository directory');ap.add_argument('--output',type=Path,default=Path(__file__).parent/'k_loop');a=ap.parse_args()
 sfile=a.input/'machine/sites230.json';tfile=a.input/'machine/k230.tm'
 assert sha(tfile)=='e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8'
 assert sha(sfile)=='400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487'
 names={'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'}
 ss=[]
 for p,ins in json.loads(sfile.read_text()):
  aa=ins.split();ss.append((p,names[aa[0]],int(aa[1]) if len(aa)>1 else None))
 root=b.tree(ss);paths=occurrences(root,OLD)
 assert paths==['111010010010111111000011','11101001001011111110011','1110100101100011','111110011']
 assert b.boundary(OLD)==b.boundary(NEW)==(0,0,False)
 nr=replace(root,OLD,NEW);nss=b.sites(nr)
 assert replace(root,OLD,MARK)==replace(nr,NEW,MARK)
 assert len(ss)==5125 and len(nss)==5121
 old=parse(tfile);new=dict(old)
 assert old[121,0]==(0,1,31) and old[121,1]==(1,1,63)
 new[121,0]=(0,1,63);new[121,1]=(1,1,13)
 a.output.mkdir(parents=True,exist_ok=True)
 outfiles={'k230_loop_basis.tm':encode(new),'sites_logical.json':b.json_bytes(nss,compact=True),'baseline_sites_logical.json':b.json_bytes(ss,compact=True)}
 for name,data in outfiles.items():(a.output/name).write_bytes(data)
 # Local canonical CFGs are small enough to display fully; the exact source
 # rewrite and closed, total macro proof then establish all-context equivalence.
 receipt=dict(status='EXACT_SOURCE_TRANSFER_PLUS_ONE_REPLACEMENT',input_table_sha256=sha(tfile),input_source_sha256=sha(sfile),
              output_table_sha256=sha(a.output/'k230_loop_basis.tm'),output_source_sha256=sha(a.output/'sites_logical.json'),
              occurrence_paths=paths,occurrences=len(paths),old_leaves=len(ss),new_leaves=len(nss),old_local=b.sites(OLD),new_local=b.sites(NEW),
              boundary_old=b.boundary(OLD),boundary_new=b.boundary(NEW),old_metrics=b.metrics(root),new_metrics=b.metrics(nr),
              collapsed_contexts_structurally_identical=True,
              macro_effect='For all natural a=R5 and b=R6, terminate with R5=a+b+1,R6=0, all other registers unchanged; normal exit.',
              old_local_execution='Repeat CD6: if positive, decrement R6, CI5, CC2 back to CD6. When zero, exit inner loop and CI5 once, then normal exit.',
              new_local_execution='CI5 once, then CD6: if positive, decrement R6 and CC2 back to CI5; if zero, normal exit.',
              exact_old_instruction_count='3*b+2',exact_new_instruction_count='3*b+2',
              induction='At each positive CD6 the natural R6 decreases by1. Old increments exactly b times in loop and once after; new increments once before each of b positive and one final zero decrement. Other registers never occur.',
              literal_edits=[{'row':[121,0],'old':old[121,0],'new':new[121,0]},{'row':[121,1],'old':old[121,1],'new':new[121,1]}],
              proof_scope='Unbounded structured source semantics by closed total context substitution. Exact binary runtime and startup are separate obligations.')
 (a.output/'source_loop_certificate.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
