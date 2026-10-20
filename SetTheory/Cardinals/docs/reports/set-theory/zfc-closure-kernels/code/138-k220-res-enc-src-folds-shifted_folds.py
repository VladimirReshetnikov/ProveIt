from invariant_search import *
R=5;N=2*R+1
I={int(q):xs for q,xs in json.loads(Path('invariant_r5.json').read_text()).items()}
inc={q:[]for q in Q}
for(q,b),(w,d,z)in T.items():
 if z in inc:inc[z].append((q,b,w,d))
eligible=[(q,-2*inc[q][0][3])for q in Q if q!=0 and q in ENGINE and len({a[3]for a in inc[q]})==1]
# Prioritize the eight-zero return scanner.
eligible.sort(key=lambda x:(x[0]not in(50,3,5,9,15,23,34),x[0]))
found=[];beg=time.monotonic();tested=0
for ri,(r,shift)in enumerate(eligible):
 for keep in Q:
  if keep==r:continue
  phi=lambda q:keep if q==r else q
  new={(q,b):(w,d+shift if z==r else d,phi(z))for(q,b),(w,d,z)in T.items()if q!=r}
  cases=[[],[]]
  for q in(keep,r):
   for x in I[q]:
    c=x>>R&1;w,d,z=T[q,c]
    goal=(x&~(1<<R))|(w<<R)
    hh=R+(shift if q==r else 0)
    cases[x>>hh&1].append((q,x,hh,phi(z),R+d+(shift if z==r else 0),goal))
  choices=[]
  for cc in(0,1):
   good=[]
   for action in itertools.product((0,1),(-1,1),[q for q in Q if q!=r]+[254]):
    tested+=1;proof=[]
    for oq,x,hh,gq,gh,gt in cases[cc]:
     q=keep;h=hh;tape=x;seen=set();matched=False
     for tick in range(1,24):
      if tick==1:w,d,z=action
      else:w,d,z=new[q,tape>>h&1]
      tape=(tape&~(1<<h))|(w<<h);q=z;h+=d
      if(q,h,tape)==(gq,gh,gt):proof.append(tick);matched=True;break
      if not 0<=h<N or q in(254,keep):break
      state=q,h,tape
      if state in seen:break
      seen.add(state)
     if not matched:break
    if len(proof)==len(cases[cc]):good.append((action,dict(collections.Counter(proof))))
   if not good:break
   choices.append(good)
  if len(choices)==2:
   item={'drop':r,'keep':keep,'head_shift':shift,'choices':choices};found.append(item);print('FOUND',json.dumps(item),flush=True)
 print('DROP',r,shift,'seconds',round(time.monotonic()-beg,1),'tested',tested,flush=True)
Path('shifted_folds_results.json').write_text(json.dumps({'found':found,'tested':tested,'seconds':time.monotonic()-beg},indent=2))
