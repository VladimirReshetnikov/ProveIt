#!/usr/bin/env python3
"""Independent root-free exact graph comparison, including two tape symmetries."""
import argparse,collections,hashlib,json
from pathlib import Path

def parse(path):
 rows={}
 for l in path.read_text().splitlines():
  l=l.strip()
  if not l or l.startswith(('#','//',';')):continue
  q,b,w,d,t=l.split();q,b,w,t=map(int,(q,b,w,t))
  assert b in(0,1)and w in(0,1)and d in('L','R') and(q,b)not in rows
  rows[q,b]=w,d,t
 states={q for q,b in rows};assert set(rows)=={(q,b)for q in states for b in(0,1)}
 hs={t for w,d,t in rows.values()}-states;assert len(hs)==1
 return rows,states,hs.pop()
def signature(table,reflect=False,complement=False):
 rows,states,halt=table;forms=[]
 for root in states:
  seen={root:0};queue=[root];result=[]
  for q in queue:
   for input_bit in(0,1):
    w,d,t=rows[q,input_bit^int(complement)]
    if t==halt:target=-1
    else:
     if t not in seen:seen[t]=len(queue);queue.append(t)
     target=seen[t]
    if complement:w=1-w
    if reflect:d='L'if d=='R'else'R'
    result.append((w,d,target))
  if len(seen)==len(states):forms.append(json.dumps(result,separators=(',',':')))
 assert forms,'No control reaches full graph'
 return min(forms)
def main():
 p=argparse.ArgumentParser();p.add_argument('--candidate',type=Path,required=True);p.add_argument('--start',type=int,required=True);p.add_argument('--census',type=Path,required=True);p.add_argument('--table-dir',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 t=parse(a.candidate);assert a.start in t[1];sig=signature(t)
 reachable={a.start};todo=[a.start]
 for q in todo:
  for b in(0,1):
   k=t[0][q,b][2]
   if k!=t[2]and k not in reachable:reachable.add(k);todo.append(k)
 x=json.loads(a.census.read_text());classes=[c for c in x['classes_below197']if c['states']==len(t[1])and c['graph_sha256']]
 matches=[]
 for c in classes:
  h=c['raw_sha256s'][0];f=a.table_dir/(h+'.tm');assert hashlib.sha256(f.read_bytes()).hexdigest()==h
  prev=parse(f)
  for refl,compl in[(False,False),(True,False),(False,True),(True,True)]:
   if sig==signature(prev,refl,compl):matches.append({'prior_graph_sha256':c['graph_sha256'],'prior_raw_sha256':h,'reflection':refl,'symbol_complement':compl,'example_path':c['occurrences'][0]})
 out={'candidate_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),'states':len(t[1]),'rows':len(t[0]),'start':a.start,'halt':t[2],'all_states_graph_reachable':len(reachable)==len(t[1]),'root_free_graph_sha256':hashlib.sha256(sig.encode()).hexdigest(),'prior_classes_compared':len(classes),'symmetries_per_class':4,'matches':matches,'graph_novel':not matches,'scope':'Exact action-preserving graph comparison. Different chosen starts permitted. Complementation changes blank symbol, and is only a stronger cosmetic check. No consistency or minimality assertion.'}
 a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':
 if not __debug__:raise RuntimeError('Assertions required')
 main()
