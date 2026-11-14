from tag_swap import *
# Primitive tag 3 is now disequality; all former equality atoms are negated.
def D(a,b):return('E',a,b)
def EQ(a,b):return N(D(a,b))
def norm(f):
 if not isinstance(f,tuple):return f
 tag,a,b=f;a,b=norm(a),norm(b)
 if tag=='I' and b==ONE and isinstance(a,tuple) and a[0]=='I' and a[2]==ONE:
  return a[1]
 return(tag,a,b)
def translate(f):
 if not isinstance(f,tuple):return f
 tag,a,b=f
 if tag=='E':return EQ(a,b)
 return norm((tag,translate(a),translate(b)))

def newheads(flags=0):return list(map(translate,heads(flags)))
def newgate(sw=0):return translate(gate(sw))
def newword(meta):
 mf,ef,uf,flags,sw,order=meta;opt=(0,mf,ef,uf)
 return emit(U('D','H'),*opt)+prefix[5:]+sum((emit(newheads(flags)[j],*opt)for j in order),[])+emit(newgate(sw),*opt)+suffix

macroattrs={}
def attrs(t):
 if isinstance(t,str):
  if t not in macroattrs:macroattrs[t]=attrs(ns[t])
  return macroattrs[t]
 if not isnode(t):return (0,0,0)
 h,l,m=attrs(t[0]);h2,l2,m2=attrs(t[1]);return1=1+max(h,h2),l+1,max(1+l,m,m2);return return1
for m in MACROS:attrs(m)
def details(t):
 ii={}
 def rec(t):
  if not isnode(t):return attrs(t)
  if t in ii:return ii[t]
  h,l,m=rec(t[0]);h2,l2,m2=rec(t[1]);a=1+max(h,h2),l+1,max(l+1,m,m2);ii[t]=a;return a
 a=rec(t);return len(ii),a,list(ii)
def cost(t):
 n,(h,l,m),choices=details(t)
 if m>6 or h>38:return n+max(0,m-6)*2+max(0,h-38),n,0,choices
 r,idx,sh=build(t);ops=opportunities_fast(r,sh);f=len(max_matching(ops));return n-f,n,f,choices

def inherited():
 # Keep maximal equal-word inherited subtrees, build a beam-optimal forest.
 trees=[];ids={};words=[];masks=[]
 def intern(t):
  if t in ids:return ids[t]
  if isnode(t):
   a,b=map(intern,t);ww=words[a]+words[b];mask=masks[a]|masks[b]
  else:ww=(t,);mask=0
  q=len(trees);trees.append(t);ids[t]=q;words.append(ww);masks.append(mask|(1<<q)if isnode(t)else 0);return q
 intern(initial)
 return trees,words,masks

def dictionary_parse(word,B=64):
 trees,words,masks=inherited();n=len(word);options=[]
 for i in range(n):options.append([q for q,w in enumerate(words)if tuple(word[i:i+len(w)])==w])
 dp=[{}for _ in range(n+1)];dp[0][0]=()
 for i in range(n):
  beam=sorted(dp[i].items(),key=lambda t:t[0].bit_count()+len(t[1]))[:B];dp[i]={}
  for mask,parts in beam:
   for q in options[i]:
    j=i+len(words[q]);m=mask|masks[q];p=parts+(q,)
    if m not in dp[j]or len(p)<len(dp[j][m]):dp[j][m]=p
 m,p=min(dp[n].items(),key=lambda t:t[0].bit_count()+len(t[1]));return m.bit_count()+len(p)-1,[trees[q]for q in p]
def balanced(parts):
 if len(parts)==1:return parts[0]
 k=len(parts)//2;return balanced(parts[:k]),balanced(parts[k:])

if __name__=='__main__':
 base=(0,0,0,0,0,tuple(range(6)))
 ww=newword(base)
 print('disequality base tokens',len(ww), 'heads',list(map(lambda h:len(emit(h)),newheads())), 'gate',len(emit(newgate())),flush=True)
 c,p=dictionary_parse(ww);t=balanced(p);print('dictionary',c,'actual',cost(t)[:3],flush=True);Path('disequality_base.json').write_text(json.dumps(encode(t),indent=2))
 best=999;records=[];start=time.time();rng=random.Random(1614)
 for i in range(30000):
  mf=rng.randrange(2);ef=rng.randrange(2);uf=0;flags=rng.randrange(8);sw=rng.randrange(2);order=list(range(6));rng.shuffle(order)
  meta=(mf,ef,uf,flags,sw,tuple(order));ww=newword(meta);t=repr_tree(ww,i);n,_=stats(t)
  if n<best:
   best=n;rec={'n':n,'meta':meta,'iteration':i,'tokens':len(ww),**encode(t)};records.append(rec);Path('disequality_shortlist.json').write_text(json.dumps(records,indent=2));print('BEST',n,meta,'tokens',len(ww),'seconds',time.time()-start,flush=True)
  if i%5000==0:print('iter',i,'best',best,flush=True)
 print('DONE',best,flush=True)
