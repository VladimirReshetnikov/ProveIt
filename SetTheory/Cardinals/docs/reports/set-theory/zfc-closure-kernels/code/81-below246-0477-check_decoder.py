from pathlib import Path
import json,collections,sys
HERE=Path(__file__).parent

def table(path):
 T={}
 for line in Path(path).read_text().splitlines():
  if line.startswith('#') or not line:continue
  q,b,w,d,t=line.split();T[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
 return T

def main():
 T=table(sys.argv[1]);roles={int(n):q for n,q in json.load(open(Path(sys.argv[2]) if len(sys.argv)>2 else HERE/'compiled24_raw_roles.json'))['roles'].items()}
 E={int(n):v for n,v in json.load(open(HERE.parent/'agent_logic/rotation_zero_candidate_24.json'))['entries'].items()}
 hints=json.load(open(HERE.parent/'agent_logic/rotation_zero_physical_hints.json'))['entries']
 bad=collections.Counter();good=collections.Counter();examples={};contexts=collections.defaultdict(set)
 for e in hints:
  q=roles[e['grammar_node']]
  for b in (0,1):
   child=e['children'][b]
   if E[child][0]!='N':continue
   target=roles[child]
   for oc in e['occurrences']:
    p=oc['path'];tape={i-len(p):int(x) for i,x in enumerate('1'+p+str(b))};tape={i-1:b for i,b in tape.items() if b};orig=tape.copy();state=q;h=0
    context=p[-8:]+str(b);contexts[q,b].add((context,target))
    for tick in range(21):
     if tick and state==target and h==1 and tape==orig:break
     if (state,tape.get(h,0)) not in T:tick=21;break
     w,d,state=T[state,tape.get(h,0)]
     if w:tape[h]=1
     else:tape.pop(h,None)
     h+=d
    else:tick=21
    if tick<=20:good[q,b]+=1
    else:
     bad[q,b]+=1;examples.setdefault((q,b),(oc['path'],e['grammar_node'],child,target,state,h))
 print('GOOD',sum(good.values()),'BAD',sum(bad.values()))
 for row,count in bad.items():print('BAD',row,count,'of',count+good[row],'example',examples[row],'contexts',sorted(contexts[row]))
if __name__=='__main__':main()
