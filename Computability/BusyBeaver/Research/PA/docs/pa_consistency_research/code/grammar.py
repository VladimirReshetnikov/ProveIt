from pathlib import Path
import re,random,collections,json
ROOT=Path(__file__).resolve().parents[1]/'data'
src=(ROOT/'pa196_program.lean').read_text()
nodes={}
def parse(toks,i=0):
    t=toks[i]
    if t=='(':
        v,j=parse(toks,i+1);assert toks[j]==')';return v,j+1
    if t=='.node':
        a,j=parse(toks,i+1);b,j=parse(toks,j);return (a,b),j
    if t=='.leaf':return parse(toks,i+1)
    if t in ('.inc','.dec','.breakTo','.continueTo'):
        return t[1:]+toks[i+1],i+2
    if t=='.halt':return 'halt',i+1
    return nodes[t],i+1
for n,e in re.findall(r'def (\w+) : Tree := (.*)',src):
    ts=re.findall(r'\.\w+|[A-Za-z]\w*|\d+|[()]',e)
    v,j=parse(ts);assert j==len(ts);nodes[n]=v
macronames=['node49','node55','node58','node70','node65','node72','node75','node142','x65']
atoms={nodes[n]:n for n in macronames}
atoms['inc1']='inc1'
def collapse(t):
    if t in atoms:return [atoms[t]]
    assert isinstance(t,tuple),t
    return collapse(t[0])+collapse(t[1])
seq=collapse(nodes['x67'])
print('SEQ',len(seq),collections.Counter(seq))
def internal(t):
    seen=set()
    def f(t):
        if isinstance(t,tuple) and t not in seen:
            seen.add(t);f(t[0]);f(t[1])
    f(t);return seen
base=internal(nodes['trie'])
fixed=internal(nodes['trie'][0])|internal(nodes['trie'][1])
# replace x67 by arbitrary atom to isolate external fixed subtrees
def subst(t,what,val):
    if t==what:return val
    return tuple(subst(x,what,val) for x in t) if isinstance(t,tuple) else t
external=subst(nodes['trie'],nodes['x67'],'HOLE')
free=internal(external)
free |= set().union(*(internal(t) for t in atoms))
print('BASE',len(base),'FREE',len(free),'AX',len(internal(nodes['x67'])),'GROUP',len(base-free))
# Generate RePair grammar with weighted random pair selection and greedy final joins.
def cost(t):return len(internal(subst(external,'HOLE',t)))
def repair(seed):
    random.seed(seed);s=[nodes.get(n,n) for n in seq]
    known=set(free)
    while len(s)>1:
        counts=collections.Counter(zip(s,s[1:]))
        # exact nonoverlap frequency
        for k in list(counts):
            counts[k]=sum(1 for i in range(len(s)-1) if s[i:i+2]==list(k))
        scored=[]
        for p,c in counts.items():
            if c==1:continue
            benefit=c-(0 if p in known else 1)
            score=benefit+random.uniform(0,2.0)
            scored.append((score,random.random(),p))
        if not scored:break
        p=max(scored)[2];known.add(p)
        new=[];i=0
        while i<len(s):
            if i+1<len(s) and (s[i],s[i+1])==p:new.append(p);i+=2
            else:new.append(s[i]);i+=1
        s=new
    # Random merge residual nodes, prioritise known nodes
    while len(s)>1:
        j=random.randrange(len(s)-1)
        opts=[i for i in range(len(s)-1) if (s[i],s[i+1]) in known]
        if opts:j=random.choice(opts)
        p=(s[j],s[j+1]);known.add(p);s[j:j+2]=[p]
    return s[0]
