#!/usr/bin/env python3
"""Independent universal positive-block fold verification, no optimizer imports.
Unmentioned tape cells are independent Boolean variables. Reads split exhaustively;
finite writes are compared exactly, so all untouched infinite tape cells agree.
"""
import argparse,json,collections,copy
from pathlib import Path
from audit_decoder_contexts import table
from check_grammar_equivalence import need,sha

def verify(O,N,P):
 keep,drop=P['keep'],P['drop'];halt=254;I={int(q):{int(k):v for k,v in a.items()}for q,a in P['invariant'].items()};states={q for q,b in O};f=lambda q:keep if q==drop else q
 need(P['headshift']==0 and P['tagoffset']is None,'unsupported relation');need(P['start_old']==P['start_new']==0 and not I[0],'all-tape initial invariant');need(set(I)==states|{halt},'invariant domain');need(all(type(v)is int and v in(0,1)for a in I.values()for v in a.values()),'Boolean invariant');need({q for q,b in N}==states-{drop},'state elimination');need(all((q,b)in O for q in states for b in(0,1)),'old total');need(all((q,b)in N for q in states-{drop} for b in(0,1)),'new total')
 hist=collections.Counter();cases=0;branches=0
 for q in sorted(states):
  for b in(0,1):
   if 0 in I[q]and I[q][0]!=b:continue
   w,d,z=O[q,b];known=dict(I[q]);known[0]=b
   # Original invariant is checked for every possible current tape satisfying it.
   for k,v in I[z].items():need((w if k+d==0 else known.get(k+d))==v,'invariant not inductive')
   stack=[(f(q),0,{},known,0)];cases+=1
   while stack:
    nq,h,writes,base,n=stack.pop();branches+=1
    def initial(k):return base[k]if k in base else ('variable',k)
    def current(k):return writes.get(k,initial(k))
    if n:
     if z==halt and nq==halt:hist[n]+=1;continue
     if z!=halt and nq==f(z)and h==d and all(current(k)==(w if k==0 else initial(k))for k in set(writes)|{0}):hist[n]+=1;continue
    need(nq!=halt,'interior/spurious halt');need(n<32,'block bound exhausted');v=current(h)
    if isinstance(v,tuple):
     for bit in(0,1):nb=base.copy();nb[h]=bit;stack.append((nq,h,writes.copy(),nb,n))
     continue
    need((nq,v)in N,'missing new row');nw,nd,nz=N[nq,v];ww=writes.copy();ww[h]=nw;stack.append((nz,h+nd,ww,base,n+1))
 return dict(status='INDEPENDENT_ALL_TAPE_POSITIVE_BLOCK_PASS',old_states=len(states),new_states=len(states)-1,invariant_guarded_rows=cases,symbolic_nodes=branches,positive_block_lengths=dict(sorted(hist.items())),maximum_block=max(hist),relation=f'State {drop} maps to {keep}; every other state, integer head, and entire binary tape is identical.',scope='All initial binary tapes and all integer head positions from state0. Original invariant independently checked inductive. Each old transition has a positive new block, no interior halt, identical complete tape and head at nonhalting endpoints. Halt endpoints preserve halting; terminal tape/head are immaterial.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--old',type=Path,required=True);ap.add_argument('--new',type=Path,required=True);ap.add_argument('--witness',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();O=table(a.old);N=table(a.new);P=json.loads(a.witness.read_bytes());out=verify(O,N,P)
 # A wrong folded row must not satisfy the universal relation.
 bad=N.copy();bad[P['keep'],0]=(0,1,254)
 try:verify(O,bad,P)
 except ValueError as e:out['negative_control']=dict(status='REJECTED',reason=str(e))
 else:raise ValueError('corrupt fold accepted')
 B=copy.deepcopy(P);B['invariant']['0']={'0':0}
 try:verify(O,N,B)
 except ValueError as e:out['invariant_negative_control']=dict(status='REJECTED',reason=str(e))
 else:raise ValueError('restricted initial tape accepted')
 out.update(old_sha256=sha(a.old.read_bytes()),new_sha256=sha(a.new.read_bytes()),witness_sha256=sha(a.witness.read_bytes()),checker_sha256=sha(Path(__file__).read_bytes()));a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
