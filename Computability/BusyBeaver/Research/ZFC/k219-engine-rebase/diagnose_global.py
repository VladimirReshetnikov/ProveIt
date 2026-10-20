#!/usr/bin/env python3
"""Capture rejected allocation and first bad decoder prefix; no relaxed acceptance."""
from pathlib import Path
from types import SimpleNamespace
import argparse,json,sys,hashlib
HERE=Path(__file__).resolve().parent;BASE=HERE.parent
sys.dont_write_bytecode=True;sys.path[:0]=[str(HERE),str(HERE/'code')]
import source_language as s,build221 as b,global_allocator as g
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def trace_failure(table,tree):
 def visit(node,prefix,state):
  if s.leaf(node):return None
  for bit in(0,1):
   if s.leaf(node[bit]):continue
   tape={i:int(x)for i,x in enumerate(prefix+str(bit))};tape[-1]=1;before=tape.copy();head=len(prefix);q=state;trace=[]
   for tick in range(100):
    if head==len(prefix)+1:break
    if head not in tape:return dict(prefix=prefix,branch=bit,state=state,reason='read outside known prefix',trace=trace)
    read=tape[head];w,d,z=table[q,read];trace.append([q,head,read,w,d,z]);tape[head]=w;head+=d;q=z
   if tape!=before or head!=len(prefix)+1:return dict(prefix=prefix,branch=bit,state=state,reason='prefix changed or did not advance',trace=trace)
   failure=visit(node[bit],prefix+str(bit),q)
   if failure:return failure
  return None
 return visit(tree,'',84)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();assert not a.out.exists();a.out.mkdir(parents=True)
 oldtable=b.read_table((BASE/'candidate-k219/k219.native.tm').read_bytes());old=s.tree(json.loads((BASE/'candidate-k219/sites219.json').read_text()))
 for name in('RAB-left','RBC-left','RCA-right'):
  source=BASE/f'k219-pivot-fusion/results/membership-protected/{name}/sites.json';new=s.tree(json.loads(source.read_text()));d=a.out/name;d.mkdir();captured={}
  def checked(table,tree):
   if tree!=old:captured['table']=dict(table)
   return b.decoder_map(table,tree)
  try:g.compile_tree(s,SimpleNamespace(decoder_map=checked),oldtable,old,new)
  except ValueError as exc:
   assert 'table'in captured;table=captured['table'];(d/'rejected.native.tm').write_bytes(b.table_bytes(table))
   failure=trace_failure(table,new);assert failure
   diff=[[q,bit,list(row),list(table[q,bit])if(q,bit)in table else None]for(q,bit),row in sorted(oldtable.items())if table.get((q,bit))!=row]
   dump(d/'result.json',dict(status='REJECTED_DECODER_PREFIX_DIAGNOSED',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),raw_states=len(table)//2,original_error=repr(exc),failure=failure,old_row_delta=diff,scope='Rejected diagnostic table; original exact decoder check was not weakened.'))
   print(name,len(table)//2,failure['prefix'],failure['state'],failure['trace'],flush=True)
  else:raise AssertionError('Expected preserved failure')
if __name__=='__main__':main()
