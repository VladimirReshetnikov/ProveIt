#!/usr/bin/env python3
"""Independent literal-only cross-language/source/frame audit; invokes no compiler."""
from pathlib import Path
import json,re,hashlib
R=Path('/home/codex/.codex/worktrees/ec20/Proofs'); C=R/'Computability/BusyBeaver/Research/ZFC/candidate-k215'; L=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'; Q=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215'; F=R/'Computability/BusyBeaver/Research/ZFC/k225-formal'
pins={}
def read(p):
 b=p.read_bytes();pins[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)};return b.decode()
def tm(p):
 t={}
 for ln in read(p).splitlines():
  if not ln or ln.startswith('#'): continue
  q,b,w,d,n=ln.split();key=(int(q),int(b));assert key not in t;t[key]=(int(w),d,int(n))
 return t
def block(s,start,end):return s.split(start,1)[1].split(end,1)[0]
def action(w,d,n):return(int(w=='true'),'R' if d in ('true','R') else 'L',int(n))
def rows_to_tm(rows):return {(i,b):tuple(r[b]) for i,r in enumerate(rows) for b in (0,1)}
accepted=tm(C/'k215.tm'); native=tm(C/'k215.native.tm'); assert len(accepted)==len(native)==430
ld=read(L/'KDense215.lean'); b=block(ld,'def rows215',']'); pats=re.findall(r'\(\((true|false), (true|false), (\d+)\), \((true|false), (true|false), (\d+)\)\)',b);assert len(pats)==215
lean=rows_to_tm([(action(*p[:3]),action(*p[3:])) for p in pats]);assert lean==accepted
qd=read(Q/'Table215.v');pats=re.findall(r'\((true|false), (L|R), (\d+), (true|false), (L|R), (\d+)\)',qd);assert len(pats)==215
rocq=rows_to_tm([(action(*p[:3]),action(*p[3:])) for p in pats]);assert rocq==accepted
labels=list(map(int,re.findall(r'\d+',block(ld,'def denseLabels : List Nat := [',']'))));assert len(labels)==len(set(labels))==215
qlabels=list(map(int,re.findall(r'\d+',block(read(Q/'Dense215.v'),'Definition dense_labels : list nat := [',']'))));assert qlabels==labels+[230]
ren={301:102,302:120,254:230};nr={(ren.get(q,q),b):(w,d,ren.get(n,n)) for(q,b),(w,d,n)in native.items()};assert len(nr)==430
assert {(labels[q],b):(w,d,(labels+[230])[n]) for(q,b),(w,d,n)in accepted.items()}==nr
assert tm(F/'lean215/k215_k230labels.tm')==nr
assert tm(F/'rocq/rocq-extension/inputs/215/table.tm')==accepted
assert tm(F/'rocq/rocq-extension/inputs/215/table_k230labels.tm')==nr
lt=read(L/'KTable215.lean');body=block(lt,'def table215 :',']');lines=[x.strip().rstrip(',')for x in body.splitlines()[1:] if x.strip()];assert len(lines)==230
sparse={}
for q,line in enumerate(lines):
 if line=='(none, none)':continue
 p=re.fullmatch(r'\(some \((true|false), (true|false), (\d+)\), some \((true|false), (true|false), (\d+)\)\)',line);assert p,line
 sparse[q,0]=action(*p.groups()[:3]);sparse[q,1]=action(*p.groups()[3:])
assert sparse==nr
# Independent source expansion, parsing only literal node dictionaries.
ops={'inc':'CI','decnz':'CD','brk':'CB','cont':'CC','node':'CN','halt':'CH'}
ls=read(L/'KSource215.lean');body=block(ls,'def p215Nodes', 'def p215 :');nodes=[]
for i,a,x,b,y in re.findall(r'\| (\d+) => \(\(\.(\w+)(?: (\d+))?\), \(\.(\w+)(?: (\d+))?\)\)',body):
 assert int(i)==len(nodes);nodes.append(((ops[a],int(x or 0)),(ops[b],int(y or 0))))
assert len(nodes)==179
qp=read(Q/'Prog215.v');body=block(qp,'Definition p215_tab','].'); qnodes=[]
for a,x,b,y in re.findall(r'\((C[I DBNCH]+)\s*(\d*)\s*,\s*(C[I DBNCH]+)\s*(\d*)\)',body):
 qnodes.append(((a,int(x or 0)),(b,int(y or 0))))
assert qnodes==nodes,(len(qnodes),len(nodes))
def unfold(e,path=''):
 op,x=e
 if op!='CN':return [[path,op,x]]
 assert 0<=x<len(nodes)
 return unfold(nodes[x][0],path+'0')+unfold(nodes[x][1],path+'1')
sites=unfold(('CN',178));delivered=json.loads(read(C/'sites215.json'));assert sites==delivered;assert len(sites)==4751
assert json.loads(read(F/'rocq/rocq-extension/inputs/215/sites.json'))==sites
# Decode cp13's finite right tape, without running the TM.
cp=read(L/'KBoot215Chunk012.lean'); rhs=block(cp,'def cp13 : LConf :=','theorem block13');bs=re.findall(r'\[([^]]*)\]',rhs,re.S);assert len(bs)==2
left=[v=='true'for v in re.findall(r'true|false',bs[0])];right=[v=='true'for v in re.findall(r'true|false',bs[1])];assert left==[True]+[False]*9;assert right[:66]==[False]*65+[True]
rest=right[66:];vs=[]
while rest:
 assert rest[0]==False;rest=rest[1:];n=0
 while rest and rest[0]:n+=1;rest=rest[1:]
 assert n>=1;vs.append(n-1)
assert vs==[0,0,0,0,0,0,4,0,0]+[1]*40
boot=read(L/'KBoot215.lean');literal=list(map(int,re.findall(r'\d+',block(boot,'def bootVs : List Nat := [',']'))));assert literal in ([0,0,0,3,0,0,3,0,0],[0,0,0,0,0,0,4,0,0])
qboot=read(Q/'Boot230.v');qvs=list(map(int,re.findall(r'\d+',block(qboot,'Definition boot_regs : list nat := [',']'))));assert qvs==vs[:9]
out={'status':'PASS_LITERAL_BINDINGS','scope':'Own static literal parser only; no compiler, proof checker, or machine execution. Bootstrap mismatch is recorded separately from table/source PASS.','working_states':215,'actions':430,'dense_target_range':[0,215],'native_relabeling':ren,'lean_and_rocq_dense_tables_match_accepted':True,'lean_sparse_table_matches_native':True,'source_nodes':len(nodes),'source_leaves':len(sites),'lean_rocq_source_equals_accepted':True,'cp13_physical_registers':vs[:9],'cp13_spares':40,'cp13_gap':65,'lean_boot_literal':literal,'lean_boot_matches_checkpoint':literal==vs[:9],'rocq_boot_matches_checkpoint':True,'pins':pins}
p=Path('/tmp/k215-endpoint-audit/literal-bindings.json');p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='pins'},indent=2))
