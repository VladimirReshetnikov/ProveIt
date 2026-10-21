import complement_quantifier as c
import functools,collections,json,time
c.spans['GEN']=(40,121)
s,m=c.s,c.m

def nodes(t):return {t}if s.leaf(t)else {t}|nodes(t[0])|nodes(t[1])
allnodes=nodes(c.tree);ids={};trees=[];children=[]
def intern(t):
 if t in ids:return ids[t]
 cc=()if s.leaf(t)else(intern(t[0]),intern(t[1]))
 k=len(trees);ids[t]=k;trees.append(t);children.append(cc);return k
root=intern(c.tree)
@functools.cache
def closure(k):return frozenset([k])if not children[k]else frozenset([k])|closure(children[k][0])|closure(children[k][1])
@functools.cache
def shape(k):
 if not children[k]:return(0,0,0)
 a,b=map(shape,children[k]);return(1+max(a[0],b[0]),1+a[1],max(a[2],b[2],1+a[1]))
closed=collections.defaultdict(list)
for n in allnodes:
 if s.boundary(n)==(0,0,False):closed[m.flat(n)].append(intern(n))

def optimize(tokens,base,beam=2):
 nn=len(tokens);dp={};ww=[m.flat(c.mac[x])for x in tokens]
 for length in range(1,nn+1):
  for i in range(nn-length+1):
   j=i+length;w=sum(ww[i:j],());cands=set(closed.get(w,[]))
   if length==1:cands.add(intern(c.mac[tokens[i]]))
   for cut in range(i+1,j):
    for l in dp[i,cut]:
     for r in dp[cut,j]:
      k=intern((trees[l],trees[r]))
      if shape(k)[2]<=6:cands.add(k)
   def rank(k):return(len(closure(k)-base),shape(k)[2],shape(k)[0],k)
   dp[i,j]=sorted(cands,key=rank)[:beam]
   if not dp[i,j]:raise ValueError(('no candidate',i,j))
 return [trees[k]for k in dp[0,nn]]

results=[]
mode='coforall';fs=c.gen_transformed(mode);changed={name for name in fs if fs[name]!=c.forms[name]};skel=c.tree
for name in sorted(changed,key=lambda n:c.spans[n][0],reverse=True):skel=m.splice(s,skel,*c.spans[name],('HOLE',name))
base=frozenset(intern(n)for n in nodes(skel)if all(p[0]!='HOLE'for p in m.flat(n)))
for ordername,order in [('large',sorted(changed,key=lambda n:len(c.postfix(fs[n])),reverse=True)),('small',sorted(changed,key=lambda n:len(c.postfix(fs[n]))))]:
 chosen={};workingbase=base
 for name in order:
  begin=time.time();ws=c.postfix(fs[name]);choices=optimize(ws,workingbase,beam=2);chosen[name]=choices[0];workingbase=workingbase|closure(intern(choices[0]));print('OPT',ordername,name,'tokens',len(ws),'added',len(workingbase-base),'seconds',round(time.time()-begin,2),'pool',len(trees),flush=True)
 rr=c.tree
 for name in sorted(changed,key=lambda n:c.spans[n][0],reverse=True):rr=m.splice(s,rr,*c.spans[name],chosen[name])
 met=s.metrics(rr);assert s.graph_arithmetic(s.sites(rr))[0]==s.graph_intervals(s.sites(rr));result={'mode':mode,'order':ordername,'metrics':met,'order_names':order};print('RESULT',result,flush=True);results.append(result);(c.H/(mode+'.'+ordername+'.opt.sites.json')).write_bytes(s.compact(s.sites(rr)))
(c.H/'complement_quantifier_optimized_results.json').write_text(json.dumps(results,indent=2)+'\n')
