import pathlib,json,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
# standalone parser: no supplied imports.
def table(p):return {(int(q),int(b)):(int(w),1 if d=='R' else -1,int(z))for q,b,w,d,z in (l.split()for l in p.read_text().splitlines()if l and not l.startswith('#'))}
PHY=(6,2,0,4,3,7,8,5,1)
def frame(pc,regs,spares,gap=0):
 vals=[None]*9
 for i,j in enumerate(PHY):vals[j]=regs[i]
 ones={-1,56+gap}|{i for i,b in enumerate(pc)if b=='1'};p=57+gap
 for v in vals+spares:p+=1;ones.update(range(p,p+v+1));p+=v+1
 return ones

def clean(q,h,ones):
 if q!=84 or h-1 not in ones or any(x<h-1 for x in ones):return False
 right=sorted(x for x in ones if x>=h+44)
 if not right or right[0]<h+56:return False
 p=right[0]+1;last=max(ones);vals=[]
 while p<last:
  if p in ones or p+1 not in ones:return False
  st=p+1;p=st
  while p in ones:p+=1
  vals.append(p-st-1)
 return p==last+1 and len(vals)>=10

def run(t,pc,regs,spares,lim=100000):
 ones=frame(pc,regs,spares);q=84;h=0;tr=[]
 for k in range(lim):
  if k and clean(q,h,ones):return {'steps':k,'state':q,'head':h,'ones':sorted(ones),'trace':tr}
  if(q,int(h in ones))not in t:return {'steps':k,'state':q,'head':h,'ones':sorted(ones),'trace':tr,'halt':True}
  b=int(h in ones);w,d,z=t[q,b];tr.append([k,q,h,b,w,d,z]);ones.add(h)if w else ones.discard(h);h+=d;q=z
 return {'limit':lim}
R=pathlib.Path(__file__).resolve().parents[1];O=R/'audit'
a=json.loads((R/'source_search/candidate207.sites.json').read_text());oldp=R.parent/'u209_reduction_20261029/table_search/candidate_89145587/native.tm';oldt=table(oldp);newt=table(R/'source_search/candidate207.native.tm');oldsites=json.loads((R.parent/'u209_reduction_20261029/release/stage/u208_research_2026-10-29/machine/variant_plain/u208.sites.json').read_text());ix=next(i for i,x in enumerate(a)if x==['0011001001100','CD',5]);reports=[]
for v in range(4):
 regs=[0]*9;regs[3]=v
 old=run(oldt,oldsites[ix][0],regs,[0]);new=run(newt,a[ix][0],regs,[0]);reports.append({'ordinal':ix,'regs':regs,'oldsite':oldsites[ix],'newsite':a[ix],'old':old,'new':new});print(ix,regs,'old',old.get('steps'),old.get('head'),'new',new.get('steps'),new.get('head'),'equal',old.get('ones')==new.get('ones'))
(O/'candidate207_concrete.json').write_text(json.dumps(reports,indent=2)+'\n')
