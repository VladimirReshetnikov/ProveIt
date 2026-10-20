from pathlib import Path
import json,sys,collections,hashlib,argparse
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[6]
sys.path.insert(0,str(ROOT/'Computability/BusyBeaver/Research/ZFC/k218-quantifier-stability/pricing'))
import source_language as s
import build221 as b

def replace(t,old,new):
 if t==old:return new
 if s.leaf(t):return t
 return replace(t[0],old,new),replace(t[1],old,new)

def candidates(seed,out):
 src=json.loads((seed/'sites218.json').read_text());tree=s.tree(src);table=b.read_table((seed/'k218.native.tm').read_bytes());groups,paths=b.decoder_map(table,tree)
 incoming=collections.defaultdict(set)
 for key,act in table.items():incoming[act[2]].add(key)
 basegraph=s.graph_arithmetic(src)[0]; kept=[]; stats=collections.Counter()
 for q,ns in sorted(groups.items()):
  if len(ns)!=1:continue
  node=next(iter(ns))
  for edge in (0,1):
   r=table[q,edge][2]
   if s.leaf(node[edge]) or len(groups[r])!=1 or groups[r]!={node[edge]}:continue
   if q==r or incoming[r]!={(q,edge)}:continue
   if not all(table[z,bit][:2]==(bit,1) for z in (q,r) for bit in (0,1)):continue
   stats['pure_unique']+=1
   if edge==0:
    (A,B),C=node;newnode=A,(B,C)
    actions=[(q,0,table[r,0][2]),(q,1,r),(r,0,table[r,1][2]),(r,1,table[q,1][2])]
   else:
    A,(B,C)=node;newnode=(A,B),C
    actions=[(q,0,r),(q,1,table[r,1][2]),(r,0,table[q,0][2]),(r,1,table[r,0][2])]
   if not all(s.boundary(x)==(0,0,False) for x in (A,B,C)):continue
   stats['closed']+=1
   newtree=replace(tree,node,newnode);rows=s.sites(newtree)
   if rows[:37]!=src[:37]:stats['initial37_changed']+=1;continue
   met=s.metrics(newtree)
   if met['maximum_zero_run']>6:stats['zero_run_too_long']+=1;continue
   assert [x[1:] for x in rows]==[x[1:] for x in src]
   assert s.graph_arithmetic(rows)[0]==basegraph==s.graph_intervals(rows)
   tt=dict(table)
   for z,bit,target in actions:tt[z,bit]=bit,1,target
   try:gg,_=b.decoder_map(tt,newtree)
   except ValueError as e:stats['decoder_failed']+=1;continue
   # Every actual prefix maps to the transformed old role, except the rotated child.
   expected={z:{replace(n,node,newnode) for n in old} for z,old in groups.items()}
   expected[r]={newnode[1-edge]}
   if dict(gg)!=expected:stats['binding_failed']+=1;continue
   name=f'q{q}-r{r}-edge{edge}';d=out/name;d.mkdir(parents=True)
   (d/'native.tm').write_bytes(b.table_bytes(tt));(d/'sites.json').write_bytes(s.compact(rows))
   entry=dict(name=name,q=q,r=r,edge=edge,occurrences=len(paths[q]),metrics=met,changed_rows=[list(k)+list(tt[k]) for k in sorted(tt) if tt[k]!=table[k]])
   kept.append(entry)
 result=dict(seed=str(seed),stats=stats,rotations=kept,scope='Pure one-child unique-incoming closed rotations; exact word, two CFGs and complete decoder-prefix relation. No primitive runtime/startup claim.')
 (out/'census.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser(description='Reconstruct the bounded one-rotation source family.')
 ap.add_argument('--output',type=Path,required=True)
 args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=False)
 for name,p in [('primary','candidate-k218'),('contextual','candidate-k218/alternatives/contextual/machine')]:
  out=args.output/name;out.mkdir()
  candidates(ROOT/'Computability/BusyBeaver/Research/ZFC'/p,out)
