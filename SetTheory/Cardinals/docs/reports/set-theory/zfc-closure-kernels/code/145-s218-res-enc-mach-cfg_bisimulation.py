from pathlib import Path
import sys,json,collections
sys.path.insert(0,str(Path(__file__).parent/'support/k221/portable'))
import source_language as s
rows=json.loads(Path(sys.argv[1]).read_text());G,_=s.graph_arithmetic(rows);assert G==s.graph_intervals(rows)
J={}
for i in range(len(G)):
 todo=[];seen=set();j=i
 while j not in J and G[j][0][0]=='identity' and j not in seen:
  todo.append(j);seen.add(j);j=G[j][1][0]
 if j in J:k=J[j]
 elif j in seen:k=-1
 else:k=j;J[j]=j
 for q in todo:J[q]=k
active=sorted(set(J.values()));A={-1:(('diverge',),[])}
for i in active:
 if i<0:continue
 op,tg=G[i];A[i]=(tuple(op),[J[t]for t in tg])
def partition(keys):
 ids={};out={}
 for i,key in keys:out[i]=ids.setdefault(key,len(ids))
 return out
P=partition((i,A[i][0])for i in active);rounds=0
while True:
 Q=partition((i,(A[i][0],tuple(P[t]for t in A[i][1])))for i in active);rounds+=1
 if Q==P:break
 P=Q
C={i:P[J[i]]for i in range(len(G))};counts=collections.Counter(C.values());nontrivial=[(k,v)for k,v in counts.items()if v>1]
r={'sites':len(G),'active_actions':len(active),'classes':len(set(P.values())),'refinement_rounds':rounds,'duplicate_classes':len(nontrivial),'max_class':max(counts.values()),'site_classes':[C[i]for i in range(len(G))],'identity_closure':[J[i]for i in range(len(G))]}
# Check the returned relation is a labeled graph bisimulation after identity closure.
for i in active:
 for j in active:
  if P[i]==P[j]:assert A[i][0]==A[j][0] and [P[x]for x in A[i][1]]==[P[x]for x in A[j][1]]
base=Path(sys.argv[2]);base.with_suffix('.json').write_text(json.dumps(r,indent=2));base.with_suffix('.in').write_text(''.join(f'{pc} {op} {a if a is not None else -1} {C[i]}\n'for i,(pc,op,a)in enumerate(rows)))
print({k:v for k,v in r.items()if k not in('site_classes','identity_closure')})
