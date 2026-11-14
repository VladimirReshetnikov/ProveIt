#!/usr/bin/env python3
"""Compile a re-associated PA196 AX macro word and synthesize 3-step folds.

The mathematical simulation proof must separately check source CFG equality
and full runtime; this file only constructs/counts the decoder and certifies
finite local folds using complete incoming predecessor-bit invariants.
"""
import collections,functools,itertools,json,pathlib,re,sys
HERE=pathlib.Path(__file__).resolve().parent
BB=HERE.parent/'bb196'
sys.path.insert(0,str(HERE.parent/'history209'))
import grammar_search as g

MACRO={'A':166,'C':90,'D':98,'G':221,'H':12,'J':69,'K':213,'L':194,'P':19,'i':61}
def tuples(x):return tuple(map(tuples,x)) if isinstance(x,list) else x
@functools.lru_cache(None)
def native():
 labels=json.loads(re.search(r'def labels : List Nat := (\[.*\])',(BB/'PA196/Conjugacy.lean').read_text()).group(1))
 t={}
 for line in (BB/'data/pa196.tm').read_text().splitlines():
  q,b,w,d,n=line.split();t[labels[int(q)],int(b)]=(int(w),d,labels[int(n)])
 return t
@functools.lru_cache(None)
def macro_info():return g.get_macro_tree()
def compile_tree(tree,baseline_names=False):
 old=native();T={k:a for k,a in old.items() if k[0]<1300};states={};inverse={};edges=[]
 ns,mac,base=macro_info()
 if baseline_names:
  def cv(t):return mac[t] if t in mac else (cv(t[0]),cv(t[1]))
  states={cv(ns['x'+str(i)]):1300+i for i in range(68)}
 def number(t):
  if isinstance(t,str):return MACRO[t] if t!='X' else None
  if t not in states:states[t]=2000+len(states)
  q=states[t]
  if q in inverse:return q
  inverse[q]=t
  for b in(0,1):
   u=t[b]
   if u=='X':
    if b!=1:raise ValueError('break must be right child')
    T[q,b]=(0,'L',302)
   else:T[q,b]=(b,'R',number(u))
  return q
 root=number(tree)
 for k,a in list(T.items()):
  if k[0]<1300 and a[2]>=1300:
   if a[2]!=1367:raise ValueError(('unexpected external entry',k,a))
   T[k]=(a[0],a[1],root)
 return T,inverse,root
def states(T):return sorted({q for q,b in T})
def tag_states(T,start=74):
 incoming=collections.defaultdict(list)
 for k,a in T.items():incoming[a[2]].append((k,a))
 tag={}
 for q,rows in incoming.items():
  if q!=start and rows and all(a[1]=='R' and a[0]==rows[0][1][0] for k,a in rows):tag[q]=rows[0][1][0]
 return tag,incoming
def helpers(T,acts,b):
 result=[]
 for h in states(T):
  a0,a1=T[h,0],T[h,1]
  if a0[:2]!=(0,'R') or a1[:2]!=(1,'R'):continue
  if T.get((a0[2],b))==acts[0] and T.get((a1[2],b))==acts[1]:result.append(h)
 return result
def candidates(T,internal):
 tag,_=tag_states(T);cs=[]
 index=collections.defaultdict(list)
 for h in states(T):
  a0,a1=T[h,0],T[h,1]
  if a0[:2]!=(0,'R') or a1[:2]!=(1,'R'):continue
  for b in(0,1):
   if (a0[2],b) in T and (a1[2],b) in T:index[b,T[a0[2],b],T[a1[2],b]].append(h)
 # Only body pairs; untouched old framework can be used as helpers/donors.
 for s,t in itertools.combinations(sorted(internal),2):
  if s not in tag or t not in tag or tag[s]==tag[t]:continue
  opts=[];changed=[]
  for b in(0,1):
   a0,a1=T[s,b],T[t,b]
   if a0==a1:opts.append([None]);continue
   if a0[:2]!=(b,'R') or a1[:2]!=(b,'R'):break
   act={tag[s]:a0,tag[t]:a1};hs=index[b,act[0],act[1]]
   if not hs:break
   opts.append(hs);changed.append(b)
  if len(opts)==2:
   for hh in itertools.product(*opts):
    cs.append({'s':s,'t':t,'helpers':hh,'tags':(tag[s],tag[t])})
 return cs
def make_fold(T,selection):
 projection={q:q for q in states(T)};projection[254]=254
 for c in selection:projection[c['t']]=c['s']
 new={}
 for (q,b),(w,d,t) in T.items():
  if projection[q]!=q:continue
  new[q,b]=(w,d,projection[t])
 for c in selection:
  for b,h in enumerate(c['helpers']):
   if h is not None:new[c['s'],b]=(b,'L',projection[h])
 return new,projection
def verify_three_step(T,new,proj,c):
 # Full 2-cell opaque-exterior identity. Reject any branch touching exterior.
 for old,tag in zip((c['s'],c['t']),c['tags']):
  for b in(0,1):
   initial={-1:tag,0:b};tape=initial.copy();q=proj[old];p=0
   w,d,r=T[old,b];expect=initial.copy();expect[0]=w
   endpoint=(proj[r],1 if d=='R' else -1,expect)
   good=False
   for step in range(1,4):
    if p not in tape or (q,tape[p]) not in new:return False
    w,d,r=new[q,tape[p]];tape[p]=w;p+=1 if d=='R' else -1;q=r
    if(q,p,tape)==endpoint:good=True;break
   if not good:return False
 return True
def valid_selection(T,selection):
 used=[q for c in selection for q in(c['s'],c['t'])]
 if len(set(used))!=len(used):return False
 new,p=make_fold(T,selection)
 return all(verify_three_step(T,new,p,c) for c in selection)
def best_selection(T,internal):
 cs=[c for c in candidates(T,internal) if valid_selection(T,[c])]
 best=[]
 def search(i,chosen,used):
  nonlocal best
  if len(chosen)+(len(cs)-i)<=len(best):return
  if i==len(cs):
   if len(chosen)>len(best):best=chosen.copy()
   return
  c=cs[i]
  if c['s'] not in used and c['t'] not in used:
   chosen.append(c)
   if valid_selection(T,chosen):search(i+1,chosen,used|{c['s'],c['t']})
   chosen.pop()
  search(i+1,chosen,used)
 search(0,[],set())
 return best
def price(tree):
 T,internal,root=compile_tree(tree)
 selected=best_selection(T,internal)
 return len(states(T))-len(selected),selected
@functools.lru_cache(None)
def source_metrics(tree):
 """Full source path height and longest zero run after AX substitution."""
 ns,mac,base=macro_info();expand={v:k for k,v in mac.items()}
 @functools.lru_cache(None)
 def metric(t):
  if g.isleaf(t):return (0,0,0)
  a,b=metric(t[0]),metric(t[1]);left=1+a[1]
  return (1+max(a[0],b[0]),left,max(left,a[2],b[2]))
 def ex(t):return expand[t] if isinstance(t,str) else (ex(t[0]),ex(t[1]))
 replacement=ex(tree)
 def subst(t):
  if t==ns['x67']:return replacement
  return t if g.isleaf(t) else (subst(t[0]),subst(t[1]))
 height,left,zeros=metric(subst(ns['trie']))
 return {'max_path_bits':height,'max_consecutive_zeros':zeros,'root_left_height':left}
def main():
 args=sys.argv[1:]
 if not args or args[0]=='baseline':tree=g.get_macro_tree()[2];name='baseline';bn=True
 else:tree=tuples(json.loads(pathlib.Path(args[0]).read_text()));name=pathlib.Path(args[0]).stem;bn=False
 T,internal,root=compile_tree(tree,bn);cs=candidates(T,internal)
 print(name,'states',len(states(T)),'body',len(internal),'fold options',len(cs),flush=True)
 for c in cs:
  print('PAIR',c,'words',*[g.word(internal[q]) for q in (c['s'],c['t'])],flush=True)
 (HERE/(name+'_compiler.json')).write_text(json.dumps({'tree':tree,'root':root,'table':[[q,b,*a] for(q,b),a in sorted(T.items())],'internal':internal,'candidates':cs},indent=2)+'\n')
 if name=='baseline':
  deleted={1304:1307,1311:1331,1315:1305,1323:1355,1325:1345,1351:1350}
  selection=[]
  old=native()
  for t,s in deleted.items():
   hh=tuple(old[s,b][2] if old[s,b][1]=='L' else None for b in(0,1))
   tags=tag_states(T)[0]
   selection.append({'s':s,'t':t,'helpers':hh,'tags':(tags[s],tags[t])})
  print('BASELINE6VALID',valid_selection(T,selection))
  new,p=make_fold(T,selection)
  print('BASELINE_EXACT',new==old)
if __name__=='__main__':main()
