# New experiment assembled in this study. Imported dependencies and baseline search
# attribution are recorded in PROVENANCE.json and NOTICE.txt.
from pathlib import Path
import sys,json,random,collections,shutil,argparse
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description="Experimental mixed-radix 3/6 source compiler; no small-machine theorem.")
ap.add_argument('--construction-dir',type=Path,default=HERE/'upstream/construction')
ap.add_argument('--profiles-dir',type=Path,default=HERE/'profiles')
ap.add_argument('--search-dir',type=Path,default=HERE/'upstream/nested2')
args=ap.parse_args()
BASE=args.construction_dir.resolve()
PROFILES=args.profiles_dir.resolve()
sys.path.insert(0,str(BASE));import compiler as c,baseline_tools as b
INC=('leaf','inc',1);BREAK=('leaf','breakTo',1)
O=c.raw_nodes();O['node61']=(INC,'node60');O['node163']=('node6','node54')
raw,_,_=c.build(c.read_grammar(BASE/'inputs/pa194.grammar.json'))
raw={k:v for k,v in raw.items() if k[0]<1300};raw[190,0]=(0,True,61);raw[190,1]=(1,True,99);raw[164,1]=(1,True,114)
names={'node49':19,'node55':98,'node58':12,'node70':166,'node65':90,'node72':69,'node75':213,'node142':194,'node150':221,INC:61,BREAK:-1}
def word(t):
 if t=='node60':return [61]*2
 if t=='node61':return [61]*4
 if c.isnode(t):return word(t[0])+word(t[1])
 return [names[t]]
old=word(c.read_grammar(BASE/'inputs/pa194.grammar.json'))

def attrs(t,nodes):
 if isinstance(t,str):return attrs(nodes[t],nodes)
 if not c.isnode(t):return (0,0,0,0,int(t[1]=='inc'))
 a=attrs(t[0],nodes);d=attrs(t[1],nodes)
 return (1+max(a[0],d[0]),1+a[1],max(1+a[1],a[2],d[2]),max(a[3],d[3],1+a[1] if a[4] else 0),a[4])

def treecode(t):
 vals=[];ids={}
 def go(t):
  if t in ids:return ids[t]
  if isinstance(t,int):x=(0,t,-1,-1)
  else:x=(1,go(t[0]),go(t[1]),0)
  ids[t]=len(vals);vals.append(x);return ids[t]
 root=go(t);return vals,root

SRC=args.search_dir.resolve()
for profile in ['cons6','double']:
 out=PROFILES/profile;out.mkdir(parents=True,exist_ok=True);rr=dict(raw);nn=dict(O);new=[];tags=collections.Counter();i=0
 if profile=='cons6':
  nn['mixed6mult']=('node61','node61');nn['mixed6body']=('mixed6mult',('leaf','continueTo',2));nn['mixed6loop']=(('leaf','dec',7),'mixed6body');nn['mixed6suffix']=('node46','mixed6loop');nn['mixed6root']=('node17','mixed6suffix')
  rr.update({(330,0):(0,True,105),(330,1):(1,True,331),(331,0):(0,True,58),(331,1):(1,True,332),(332,0):(0,True,62),(332,1):(1,True,333),(333,0):(0,True,334),(333,1):(0,False,16),(334,0):(0,True,190),(334,1):(1,True,190)})
  token='mixed6root'
 else:
  nn['doublebody']=('node60',('leaf','continueTo',2));nn['doubleloop']=(('leaf','dec',6),'doublebody');nn['doubleroot']=('node37','doubleloop')
  rr.update({(330,0):(0,True,28),(330,1):(1,True,331),(331,0):(0,True,21),(331,1):(1,True,332),(332,0):(0,True,99),(332,1):(0,False,16)})
  token='doubleroot'
 while i<len(old):
  if old[i]!=90:new.append(old[i]);i+=1;continue
  j=i+1
  while j<len(old) and old[j]==61:j+=1
  n=j-i-1;assert 0<=n<=3;tags[n]+=1
  if n in (1,3):new+=([330] if profile=='cons6' else [90,330])+[61]*(1 if n==1 else 4)
  else:new+=[90]+[61]*n
  i=j
 (out/'word.json').write_text(json.dumps(new));(out/'nodes.json').write_text(json.dumps(nn));(out/'fixed.native.tm').write_text(b.table_text(rr))
 def freepair(a,z):
  if a==61 and z==61:return 99
  if a==61 and z==99:return 190
  if profile=='cons6' and a==190 and z==190:return 334
  return (a,z)
 def repair(seed):
  rng=random.Random(seed);seq=list(new)
  while len(seq)>1:
   pairs=collections.Counter(zip(seq,seq[1:]));m=max(pairs.values())
   if m==1:break
   p=rng.choice([x for x,v in pairs.items()if v==m]);q=freepair(*p);dst=[];i=0
   while i<len(seq):
    if i+1<len(seq) and (seq[i],seq[i+1])==p:dst.append(q);i+=2
    else:dst.append(seq[i]);i+=1
   seq=dst
  def bracket(ss):
   if len(ss)==1:return ss[0]
   k=1 if seed%3 else rng.randint(1,min(3,len(ss)-1));return freepair(bracket(ss[:k]),bracket(ss[k:]))
  return bracket(seq)
 seeds=[];seen=set()
 for seed in range(400):
  t=repair(seed)
  if t not in seen:seen.add(t);seeds.append(t)
 lines=[str(len(rr)//2)]
 for q in sorted({q for q,b in rr}):lines.append(' '.join(map(str,[q,*rr[q,0],*rr[q,1]])).replace('True','1').replace('False','0'))
 lines.append(str(len(seeds)))
 for i,t in enumerate(seeds):
  vals,root=treecode(t);lines.append(f'{i} {len(vals)} {root}');lines.extend(' '.join(map(str,v))for v in vals)
 (out/'templates.txt').write_text('\n'.join(lines)+'\n')
 aliases={**{q:t for t,q in names.items()},99:'node60',190:'node61',330:token}
 if profile=='cons6':aliases[334]='mixed6mult'
 lines=[str(len(aliases))]
 for q,t in aliases.items():lines.append(' '.join(map(str,[q,*attrs(t,nn)])))
 (out/'leaf_attrs.txt').write_text('\n'.join(lines)+'\n')
 screen=(SRC/'screen.cpp').read_text().replace('if(fixedstate[190]&&l==99&&r==99)','if(fixedstate[190]&&l==61&&r==99)')
 if profile=='cons6':screen=screen.replace('auto k=key(l,r);auto it=intern.find(k);','if(l==190&&r==190){value[i]=334;continue;}\n  auto k=key(l,r);auto it=intern.find(k);')
 (out/'screen.cpp').write_text(screen)
 search=(SRC/'search.cpp').read_text().replace('case 190:return "\\\"node61\\\"";','case 190:return "\\\"node61\\\"";case 330:return "\\\"'+token+'\\\"";case 334:return "\\\"mixed6mult\\\"";')
 # Existing source uses an unpenalized seven-zero decoder domain; keep exact scoring.
 (out/'search.cpp').write_text(search)
 rec={'profile':profile,'old_tokens':len(old),'new_tokens':len(new),'fixed_controls':len(rr)//2,'constructor_occurrences':dict(tags),'new_macro_attrs':attrs(token,nn),'seeds':len(seeds),'unverified':True}
 (out/'prepare.json').write_text(json.dumps(rec,indent=2));print(json.dumps(rec))
