#!/usr/bin/env python3
"""Independent source-graph, literal-table and concrete-frame audit.

Uses no compiler or symbolic runtime imports. Finite concrete runs supplement,
not replace, the universal symbolic proof. Python 3 standard library only.
"""
from pathlib import Path
from collections import Counter
import argparse,ast,hashlib,json,re,time

PHY=(6,2,0,4,3,7,8,5,1)

def require(p,msg):
 if not p:raise ValueError(msg)

def read_table(path):
 rows={}
 for line in path.read_text().splitlines():
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
  require((q,b)not in rows and b in (0,1) and w in (0,1) and d in ('L','R'),'invalid row')
  rows[q,b]=(w,1 if d=='R'else -1,n)
 return rows

def parse_program(path,grammar):
 defs={}
 pat=re.compile(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b')
 for name,body in re.findall(r'^def (\w+) : Tree := \.node (.*)$',path.read_text(),re.M):
  parts=pat.findall(body);require(len(parts)==2,'unparsed definition')
  defs[name]=tuple(n if n else ('leaf',op,int(a) if a else None)for op,a,n in parts)
 rules=grammar['rules'];sites=[];intervals={}
 def walk(t,p):
  if t=='x67':return walk(grammar['root'],p)
  if isinstance(t,str):return walk(rules[t] if t in rules else defs[t],p)
  if len(t)==3 and t[0]=='leaf':
   i=len(sites);sites.append((p,t[1],t[2]));intervals[p]=(i,i+1);return i,i+1
  require(len(t)==2,'invalid tree')
  a=walk(t[0],p+'0');b=walk(t[1],p+'1');require(a[1]==b[0],'nonconsecutive tree')
  intervals[p]=(a[0],b[1]);return intervals[p]
 walk('node172','')
 def escape(p,edge,count):
  while p:
   last,p=p[-1],p[:-1]
   if last==edge:
    count-=1
    if count==0:return intervals[p][1]%len(sites) if edge=='0'else intervals[p][0]
  return 0
 ins=[]
 for i,(p,op,arg)in enumerate(sites):
  if op=='inc':row=('inc',arg,(i+1)%len(sites))
  elif op=='dec':row=('dec',arg,escape(p,'0',1),(i+1)%len(sites))
  elif op=='breakTo':row=('jump',escape(p,'0',arg))
  elif op=='continueTo':row=('jump',escape(p,'1',arg))
  elif op=='halt':row=('halt',)
  else:raise ValueError(op)
  ins.append(row)
 return sites,ins

def frame(path,regs,spares,gap):
 require(gap>len(path),'path/gap collision')
 ones={-1,gap}|{i for i,v in enumerate(path)if v=='1'}
 phy=[0]*9
 for i,j in enumerate(PHY):phy[j]=regs[i]
 pos=gap+1
 for v in phy+spares:
  pos+=1;ones.update(range(pos,pos+v+1));pos+=v+1
 return ones

def main():
 ap=argparse.ArgumentParser();ap.add_argument('packet',type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--concrete',action='store_true');args=ap.parse_args();p=args.packet
 start=time.monotonic();table=read_table(p/'pa195.tm');labels=json.loads((p/'labels.json').read_text());root=labels.index(84)
 require(set(table)=={(q,b)for q in range(195)for b in(0,1)},'195 by 2 domain')
 require(len(set(labels))==196 and labels[0]==74 and labels[-1]==254,'label bijection')
 require(all(0<=n<=195 for w,d,n in table.values()),'row target')
 native=read_table(p/'pa195.native.tm')
 require({(labels[q],b):(w,d,labels[n])for(q,b),(w,d,n)in table.items()}==native,'relabel mismatch')
 reached={0};todo=[0]
 for q in todo:
  for b in(0,1):
   n=table[q,b][2]
   if n<195 and n not in reached:reached.add(n);todo.append(n)
 require(len(reached)==195,'unreachable working labels')
 halts=[list(k)+list(v)for k,v in sorted(table.items())if v[2]==195];require(len(halts)==1,'unique halting row')
 q=0;h=0;ones=set()
 for step in range(58154):
  w,d,q=table[q,int(h in ones)]
  (ones.add if w else ones.discard)(h);h+=d
 expected=frame('100000',[2]+[0]*8,[1]*26,48)
 require(q==root and h==-2 and {x-h for x in ones}==expected,'literal startup differs')
 # Independent zipper simulation; no set-of-cells representation.
 q=0;l=[];r=[]
 for step in range(58154):
  b=r[-1]if r else 0;tail=r[:-1];w,d,q=table[q,b]
  if d==1:l.append(w);r=tail
  else:
   b=l.pop()if l else 0;r=tail+[w,b]
 require(q==root and {i for i,v in enumerate(reversed(r))if v}|{-i-1 for i,v in enumerate(reversed(l))if v}==expected,'zipper startup differs')
 # Locate the supplied authoritative source, independent of module imports.
 paths=list((p/'vendor').rglob('Program.lean'));require(len(paths)==1,'unique original Program.lean')
 sites,ins=parse_program(paths[0],json.loads((p/'grammar.json').read_text()))
 require(len(sites)==3700 and sites[25][0]=='100000','source/site count')
 export=[{'ordinal':i,'path':path,'op':op,'arg':arg,'instruction':list(ins[i])}for i,(path,op,arg)in enumerate(sites)]
 require(export==json.loads((p/'source.json').read_text()),'independent source graph mismatch')
 counts=Counter(x[0]for x in ins);require(len(sites)+counts['dec']==4815,'branch count')
 receipt={'machine_sha256':hashlib.sha256((p/'pa195.tm').read_bytes()).hexdigest(),'states':195,'rows':390,'graph_reachable_states':len(reached),'halt_label':195,'halt_transition':halts[0],'startup_steps':58154,'startup_independent_representations':2,'startup_root_state':root,'startup_head':h,'startup_ones':len(ones),'source_sites':len(sites),'source_instruction_counts':dict(counts),'source_graph_sha256':hashlib.sha256(json.dumps(export,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'source_graph_method':'subtree intervals and ancestor escape; no compiler imports','maximum_path':max(len(x[0])for x in sites),'maximum_zero_run':max(len(z)for x in sites for z in x[0].split('1'))}
 if args.concrete:
  tests=steps=largest=0
  for variant,(gap,spares)in enumerate(((48,[0]),(49,[1,0,2]),(61,[3,1]),(48,[1]*26))):
   for i,code in enumerate(ins):
    for positive in ((False,True)if code[0]=='dec'else(None,)):
     regs=[(i+3*j+variant)%4 for j in range(9)]if variant!=3 else[0]*9
     if code[0]=='dec':regs[code[1]]=1+(i%3)if positive else 0
     outregs=regs.copy();outspares=spares.copy();outgap=gap
     if code[0]=='inc':outregs[code[1]]+=1;outspares.append(1);nextsite=code[2]
     elif code[0]=='dec':
      if positive:outregs[code[1]]-=1;outgap+=1;nextsite=code[3]
      else:nextsite=code[2]
     elif code[0]=='jump':nextsite=code[1]
     else:nextsite=None
     target=frame(sites[nextsite][0],outregs,outspares,outgap)if nextsite is not None else None
     tape=frame(sites[i][0],regs,spares,gap);q=root;head=0
     for k in range(1,20001):
      require(q!=195,'premature physical halt')
      w,d,q=table[q,int(head in tape)];(tape.add if w else tape.discard)(head);head+=d
      if target is None:
       if q==195:break
      elif q==root and head==0 and tape==target:break
     else:raise ValueError(('concrete frame mismatch',variant,i,positive,q,head))
     tests+=1;steps+=k;largest=max(largest,k)
  receipt['concrete_frame_runs']={'tests':tests,'literal_transitions':steps,'longest':largest,'gaps':[48,49,61],'scope':'finite transcription/engine controls; not universal proof'}
 receipt['elapsed_seconds']=round(time.monotonic()-start,3)
 out=json.dumps(receipt,indent=2)+'\n';print(out,end='')
 if args.output:args.output.write_text(out)
if __name__=='__main__':main()
