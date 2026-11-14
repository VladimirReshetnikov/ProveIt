#!/usr/bin/env python3
"""Replay the exact composite/diagonal negation substitutions.

Checks a complete symbolic tape interface (inherited arithmetic oracles),
startup, finite CFG projections, and a closed zero-mask invariant. These are
executable certificates, not kernel checked theorems or a consistency proof.
"""
from pathlib import Path
from collections import deque,defaultdict
import sys,json,hashlib,importlib.util,argparse,itertools
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import compiler as c
import parent as bc
from support import bestcompatible_all,apply,localvalid
c.MACROS.update({'node37':28,'node64':106})
INC=('leaf','inc',1);BREAK=('leaf','breakTo',1)
TOK={'push':'node49','copyD':'node55','copyH':'node58','copyA':'node70','cons':'node65','readH':'node72','readDCons':'node75','copyGuard':'node142','compareGuard':'node150','incT':INC,'close':BREAK,'drainT':'node37','pairST':'node64'}
def flat(t):return flat(t[0])+flat(t[1])if c.isnode(t)else (t,)
def rewrite(word):
 out=[];at=[];i=0
 while i<len(word):
  if word[i:i+3]==['push','incT','cons']:at.append(i);out+=['drainT','incT','pairST'];i+=3
  else:out.append(word[i]);i+=1
 return out,at

def need(b,m):
 if not b:raise ValueError(m)
def succ(row,mask):
 op=row[0]
 if op=='halt':return()
 if op=='jump':return((row[1],mask),)
 if op=='inc':return((row[2],mask|1<<row[1]),)
 b=1<<row[1]
 return ((row[3],mask&~b),(row[3],mask))if mask&b else((row[2],mask),)
def closure(graph,entries):
 seed=(25,1);seen={seed};todo=deque([seed])
 while todo:
  pc,mask=todo.popleft()
  need(0<=pc<len(graph),'source escape')
  for z in succ(graph[pc],mask):
   if z not in seen:seen.add(z);todo.append(z)
 need(seed in seen and all(z in seen for pc,m in seen for z in succ(graph[pc],m)),'closure')
 by=defaultdict(set)
 for pc,m in seen:by[pc].add(m)
 for pc in entries:need(by[pc] and all((m&(1<<7))==0 for m in by[pc]),'register7 must be zero')
 return {'reachable_site_mask_pairs':len(seen),'entry_masks':[{'site':p,'masks':sorted(by[p])}for p in entries],'sha256':hashlib.sha256(json.dumps(sorted(seen),separators=(',',':')).encode()).hexdigest(),'initial_inclusion_and_inductive_closure_checked':True}
def branches(r):return r[2:]if r[0]in('inc','dec')else r[1:]
def normal(graph,lo,hi):
 return [r[:2]+tuple(x-lo for x in r[2:]) if r[0]in('inc','dec')else r[:1]+tuple(x-lo for x in r[1:])for r in graph[lo:hi]]
def execute(graph,pc,end,regs):
 regs=list(regs)
 for steps in range(1000000):
  if pc==end:return regs,steps
  r=graph[pc]
  if r[0]=='inc':regs[r[1]]+=1;pc=r[2]
  elif r[0]=='dec':
   if regs[r[1]]:regs[r[1]]-=1;pc=r[3]
   else:pc=r[2]
  elif r[0]=='jump':pc=r[1]
  else:raise ValueError('halt inside macro')
 raise ValueError('finite transcription check ran too long')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path,nargs='?',default=HERE);a=ap.parse_args();out=a.directory
 meta=json.loads((out/'best.score.json').read_text());family=meta['family'];parent=meta['parent']
 if parent=='original':c.machine=bc.orig_machine;c.raw_nodes=bc.orig_raw
 t=c.read_grammar(out/'best.grammar.json');old=c.read_grammar(HERE/'parent.grammar.json')
 words=json.loads((HERE/'word.original.json').read_text());newword,offsets=rewrite(words)
 need(tuple(TOK[x]for x in newword)==flat(t),'token word mismatch')
 oldsites,oldg,oldcs=c.source(old);sites,g,cs=c.source(t)
 raw=c.raw_nodes()
 def size(t):
  if isinstance(t,str):return size(raw[t])
  return size(t[0])+size(t[1])if c.isnode(t)else 1
 def first(t,start=0):
  if t=='x67':return start
  if isinstance(t,str):return first(raw[t],start)
  if not c.isnode(t):return None
  a=first(t[0],start)
  return a if a is not None else first(t[1],start+size(t[0]))
 firstpc=first('node172');need(firstpc==50,'unexpected AX start')
 running=firstpc;starts=[]
 for i,op in enumerate(words):
  if i in offsets:starts.append(running)
  running+=size(TOK[op])
 intervals=[(s,s+47)for s in starts];newstarts=[s-27*i for i,s in enumerate(starts)]
 need(len(oldg)-len(g)==27*len(starts),'site savings')
 for graph,lo,n in [(oldg,s,47)for s in starts]+[(g,s,20)for s in newstarts]:
  for pc,r in enumerate(graph):
   for dest in branches(r):
    if lo<=pc<lo+n:need(lo<=dest<=lo+n,'macro secondary exit')
    else:need(not lo<dest<lo+n,'entry inside replaced macro')
 oldblock=normal(oldg,starts[0],starts[0]+47);newblock=normal(g,newstarts[0],newstarts[0]+20)
 for p in starts:need(normal(oldg,p,p+47)==oldblock,'old blocks differ')
 for p in newstarts:need(normal(g,p,p+20)==newblock,'new blocks differ')
 def reloc(pc):
  need(not any(a<pc<b for a,b in intervals),'external target inside replacement')
  return pc-27*sum(b<=pc for a,b in intervals)
 outside=0
 for pc,r in enumerate(oldg):
  if any(a<=pc<b for a,b in intervals):continue
  expect=r[:2]+tuple(reloc(p)for p in r[2:])if r[0]in('inc','dec')else r[:1]+tuple(reloc(p)for p in r[1:])
  need(g[reloc(pc)]==expect,'outside CFG changed');outside+=1
 # Independent interval/source resolver from imported allocator library.
 spath=HERE/'code'
 sys.path.insert(0,str(spath));import source_language as sl
 opcodes={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
 encoded=[[''.join(map(str,p)),opcodes[op],arg]for p,op,arg in sites]
 # source_language returns opcodes in its own representation; compare its two
 # independent resolvers before comparing canonical operation/successor rows.
 one,_=sl.graph_arithmetic(encoded);two=sl.graph_intervals(encoded)
 need(one==two,'interval and arithmetic source resolutions disagree')
 # Root compiler uses lowercase tags and separate jump; normalize resolver form.
 for i,(effect,targets) in enumerate(one):
  op=effect[0]
  expect=('inc',effect[1],targets[0])if op=='increment' else ('dec',effect[1],targets[0],targets[1])if op=='decrement' else ('halt',)if op=='halt' else ('jump',targets[0])
  need(expect==g[i],('independent CFG differs',i,expect,g[i]))
 oldinv=closure(oldg,starts);newinv=closure(g,newstarts)
 finite=0
 for tv,wv,sv in itertools.product(range(3),repeat=3):
  regs=[3,tv,wv,4,5,6,sv,0,7];oa,_=execute(oldg,starts[0],starts[0]+47,regs);nb,_=execute(g,newstarts[0],newstarts[0]+20,regs)
  want=regs.copy();u=tv+sv;want[1]=4*((u+1)*(u+2)//2+1);want[6]=want[7]=0
  need(oa==nb==want,'macro finite control');finite+=1
 rows,idx,sh=c.build(t);folds=bestcompatible_all(rows,sh);folded,alias=apply(rows,folds)
 need(localvalid(rows,folded,alias,folds),'fold induction interface')
 val=c.validate(folded,cs);need(val['ok'],'full symbolic primitive runtime failed')
 st=bc.startup(folded,sites[25][0]);need(isinstance(st,int),'literal blank startup failed')
 text=bc.table_text(folded);(out/'machine.native.tm').write_text(text);(out/'sites.json').write_text(json.dumps(encoded)+'\n');(out/'folds.json').write_text(json.dumps(folds,indent=2)+'\n')
 rec={'family':family,'parent':parent,'old_source_sites':len(oldg),'new_source_sites':len(g),'substitutions':len(starts),'old_block_sites':47,'new_block_sites':20,'source_rows_outside_replacements_checked':outside,'independent_source_resolvers_agree':True,'old_entry_invariant':oldinv,'new_entry_invariant':newinv,'finite_transcription_controls':finite,'macro_contract':'For (T,W,S,R)=(t,w,s,0), both blocks terminate with (4*pair(t+s,1),w,0,0), all other registers unchanged.','native_table_sha256':hashlib.sha256(text.encode()).hexdigest(),'working_states':len(folded)//2,'reader_nodes':len(sh),'folds':len(folds),'symbolic_primitive_contracts':val,'startup_steps':st,'scope':'Executable source and symbolic tape checks plus mathematical local macro argument; no kernel checked end-to-end PA theorem.'}
 (out/'audit.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({k:v for k,v in rec.items()if 'invariant' not in k},indent=2))
if __name__=='__main__':main()
