from pathlib import Path
import sys,json
BASE=Path(__file__).resolve().parents[1]/'reference/pa194'
sys.path.insert(0,str(BASE/'construction'))
import compiler as c
nodes=c.raw_nodes(); rows,_=c.machine(); inc=('leaf','inc',1)
labels={k:v for k,v in c.MACROS.items() if isinstance(k,str)}
def discover(n,q):
    if not isinstance(n,str): return
    if n in labels and labels[n]!=q: raise ValueError(('label',n,q,labels[n]))
    labels[n]=q
    for bit,child in enumerate(nodes[n]):
        if rows.get((q,bit),())[:2]==(bit,True) and isinstance(child,str) and not child.startswith('x'):
            discover(child,rows[q,bit][2])
for n,q in list(labels.items()): discover(n,q)
def prim(t,p=()):
    if isinstance(t,str): return prim(nodes[t],p)
    if c.isnode(t): return prim(t[0],p+(0,))+prim(t[1],p+(1,))
    return [(t,p)]
def closed(t):
    for (_,op,k),p in prim(t):
        if op=='dec' and 0 not in p: return False
        if op=='breakTo' and p.count(0)<k: return False
        if op=='continueTo' and p.count(1)<k: return False
    return True
expansion={}
def expand(t):
    if isinstance(t,str) and t in labels:
        a,b=nodes[t];q=labels[t]
        if all(x==inc or (isinstance(x,str) and x in labels) for x in (a,b)) and closed(a) and closed(b) and all(rows[q,i][:2]==(i,True) for i in (0,1)):
            ex=(expand(a),expand(b)); expansion[t]=ex; return ex
    if c.isnode(t): return expand(t[0]),expand(t[1])
    return t
paths=[BASE/'construction/source/pa194.grammar.json',Path(__file__).resolve().parents[1]/'reference/pa194_second.grammar.json']
trees=[expand(c.read_grammar(p)) for p in paths]
pairs=[]
for n,q in labels.items():
    if q>=1300: continue
    a,b=nodes[n]
    if all(x==inc or (isinstance(x,str) and x in labels) for x in (a,b)):
        qa=61 if a==inc else labels[a];qb=61 if b==inc else labels[b]
        if rows[q,0]==(0,True,qa) and rows[q,1]==(1,True,qb): pairs.append((qa,qb,q))
allmac={**c.MACROS,**labels,inc:61}
fixed=sorted({q for q,b in rows if q<1300});out=[str(len(fixed))]
for q in fixed: out.append(' '.join(map(str,[q,*rows[q,0],*rows[q,1]])).replace('True','1').replace('False','0'))
out.append(str(len(trees)));leaves={};tokens={};physical={}
def token(t):
    if t not in tokens:
        tid=3000+len(tokens);tokens[t]=tid;leaves[tid]=t
        physical[tid]=-1 if t==c.BREAK else allmac[t]
    return tokens[t]
for j,t in enumerate(trees):
    ns=[];seen={}
    def visit(t):
        if t in seen: return seen[t]
        if t==c.BREAK or t in allmac: row=(0,token(t),-1,-1)
        else: row=(1,visit(t[0]),visit(t[1]),0)
        i=len(ns);seen[t]=i;ns.append(row);return i
    r=visit(t);out.append(f'{j} {len(ns)} {r}');out.extend(' '.join(map(str,x)) for x in ns)
HERE=Path(__file__).parent
(HERE/'closure_seeds.txt').write_text('\n'.join(out)+'\n')
def attr(t):
    if isinstance(t,str): return attr(nodes[t])
    if not c.isnode(t): return (0,0,0,0,int(t==inc))
    a,b=map(attr,t);return (1+max(a[0],b[0]),a[1]+1,max(a[1]+1,a[2],b[2]),max(a[3],b[3],1+a[1] if a[4] else 0),a[4])
attrs=[str(len(leaves))]+[' '.join(map(str,[q,*attr(t)])) for q,t in sorted(leaves.items())]
(HERE/'closure_attrs.txt').write_text('\n'.join(attrs)+'\n')
s=(HERE/'screen.cpp').read_text();patch=''.join(f'if(l=={a}&&r=={b}){{value[i]={q};continue;}}\n' for a,b,q in pairs)
s=s.replace('if(l==61&&r==61)',patch+'  if(l==61&&r==61)')
(HERE/'screen_closure.cpp').write_text(s)
s=(HERE/'search_occurrence.cpp').read_text().replace('#include "screen.cpp"','#include "screen_closure.cpp"')
a=s.index(' int rename(');b=s.index('\n void save(',a)
ss=' string jsonleaf(int t)const{int q=physical(t);switch(q){'
ss+=''.join('case '+str(q)+':return '+json.dumps(json.dumps(t,separators=(',',':')))+';' for q,t in leaves.items())
ss+='}throw runtime_error("unknown leaf");}'
s=s[:a]+ss+s[b:]
a=s.index('  if(cycle++%1000==999)');b=s.index('\n  for(int j=0;',a)
s=s[:a]+'  cycle++;'+s[b:]
a=s.index('   if(pick(1000)<3)');b=s.index('else {auto reach',a)
s=s[:a]+'   '+s[b+5:]
# Distinct source tokens may share a context-sensitive physical entry.
# Preserve source token identity in E.at, E.pair and JSON, converting only at screening.
physfn='int leaf_physical(int t){switch(physical(t)){'+''.join('case '+str(t)+':return '+str(q)+';' for t,q in physical.items())+'}throw runtime_error("unknown source token");}'
s=s.replace('struct E{',physfn+'\nstruct E{')
s=s.replace('if(t<0)v={0,physical(t),-1,-1};','if(t<0)v={0,leaf_physical(t),-1,-1};')
s=s.replace('physical(l)==194','physical(l)=='+str(tokens['node142']))
s=s.replace('physical(r)==69','physical(r)=='+str(tokens['node72']))
(HERE/'search_closure.cpp').write_text(s)
(HERE/'closure_dictionary.json').write_text(json.dumps({'labels':labels,'expansion':expansion,'pairs':pairs,'leaves':leaves,'physical':physical,'source_tokens':[(tid,t) for t,tid in tokens.items()]},indent=2)+'\n')
print('closure leaves',leaves);print('reusable pairs',len(pairs));print('expanded macro roots',list(expansion))
