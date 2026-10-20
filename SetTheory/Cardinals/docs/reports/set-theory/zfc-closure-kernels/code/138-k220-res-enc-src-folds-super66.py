from invariant_search import *
R=5;N=2*R+1;I={int(q):xs for q,xs in json.loads(Path('invariant_r5.json').read_text()).items()}
Q2=[q for q in Q if q!=198]
oldcases=[]
for x in I[66]:
 if x>>R&1:continue
 tape=x;h=R;q=66;targets={}
 for k in range(1,12):
  w,d,q=T[q,tape>>h&1];tape=(tape&~(1<<h))|(w<<h);h+=d
  if not(0<=h<N)or q==254:break
  if q!=198:targets[q,h,tape]=k
 oldcases.append((x,targets))
new={k:v for k,v in T.items()if k[0]!=198}
found=[];tested=0
for action in itertools.product((0,1),(-1,1),Q2+[254]):
 new[66,0]=action;allproof=[]
 for x,targets in oldcases:
  matched=False
  tape=x;h=R;q=66;seen=set()
  for k in range(1,24):
   w,d,q=new[q,tape>>h&1];tape=(tape&~(1<<h))|(w<<h);h+=d
   sig=q,h,tape
   if sig in targets:allproof.append((targets[sig],k));matched=True;break
   if not(0<=h<N)or q==254 or sig in seen:break
   seen.add(sig)
  if not matched:break
 if len(allproof)==len(oldcases):
  print('FOUND',action,collections.Counter(allproof));found.append({'action':action,'counts':list(collections.Counter(allproof).items())})
 tested+=1
Path('super66_results.json').write_text(json.dumps({'found':found,'tested':tested,'cases':len(oldcases)},indent=2))
print('DONE',len(found),tested,'cases',len(oldcases))
