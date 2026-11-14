from pathlib import Path
exec((Path(__file__).resolve().parents[2] / 'work/logic/word_variants.py').read_text().split('start=time.monotonic()')[0])
import heapq
from collections import defaultdict

trees=[];ids={};words=[];masks=[]
def intern(t):
    if t in ids:return ids[t]
    if isnode(t):
        a,b=map(intern,t);word=words[a]+words[b];mask=masks[a]|masks[b]
    else:word=(t,);mask=0
    q=len(trees);ids[t]=q;trees.append(t);words.append(word);masks.append(mask|(1<<q) if isnode(t) else 0);return q
intern(initial)

def parse(word,B=8):
    n=len(word);options=[]
    for i in range(n):
        options.append([q for q,w in enumerate(words) if tuple(word[i:i+len(w)])==w])
    dp=[{} for _ in range(n+1)];dp[0][0]=()
    for i in range(n):
        beam=sorted(dp[i].items(),key=lambda t:t[0].bit_count()+len(t[1]))[:B]
        dp[i]={}
        for mask,parts in beam:
            for q in options[i]:
                j=i+len(words[q]);m=mask|masks[q];p=parts+(q,)
                if m not in dp[j] or len(p)<len(dp[j][m]):dp[j][m]=p
    m,p=min(dp[n].items(),key=lambda t:t[0].bit_count()+len(t[1]))
    return m.bit_count()+len(p)-1,p

best=999;seen=0;start=time.monotonic();found=[]
for meta,word in variants():
    c,p=parse(word,8);seen+=1
    if c<best:
        best=c;print('BEST',best,meta,'parts',len(p),'seen',seen,'seconds',time.monotonic()-start,flush=True)
    if c<=68:
        found.append({'cost':c,'parts':[encode(trees[q]) if isnode(trees[q]) else {'terminal':trees[q]} for q in p],'meta':meta})
        Path('transport_candidates.json').write_text(json.dumps(found,indent=2))
    if seen%500==0:print('scanned',seen,'best',best,'found',len(found),'seconds',time.monotonic()-start,flush=True)
