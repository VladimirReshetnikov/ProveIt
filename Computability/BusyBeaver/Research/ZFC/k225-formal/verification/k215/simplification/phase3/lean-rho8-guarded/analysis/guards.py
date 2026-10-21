"""Own inert syntax analysis: no delivered code imported or executed."""
import json,re,hashlib
from pathlib import Path
from functools import cache
src=Path('/tmp/zfc-intake191/K218_Dominated_Rho8_2026-10-20/K218_Dominated_Rho8_2026-10-20/theory/evidence/CD230.v')
text=src.read_text()
def parse(s):
    ts=re.findall(r'[()]|[^\s()]+',s); i=0
    def go():
        nonlocal i
        t=ts[i]; i+=1
        if t!='(':return t
        out=[]
        while ts[i]!=')':out.append(go())
        i+=1;return tuple(out)
    out=go(); assert i==len(ts),(i,len(ts));return out
rows={int(m[1]):(m[2].split(),parse(m[3]),parse('('+m[4]+')')) for m in re.finditer(r'Lemma cd_(\d+) \((.*?) : nat\) : thm230 (.*?)\.\s*Proof\. exact \((.*?)\)\. Qed\.',text,re.S)}
assert len(rows)==107
T='T'
def imp(a,b):return T if a==T and b==T else(a,b)
def term(t,e):
    if isinstance(t,str):return T if t=='0' else e[t]
    assert len(t)==3 and t[0]=='wim',t
    return imp(term(t[1],e),term(t[2],e))
def subst(t,e):return imp(subst(t[0],e),subst(t[1],e)) if isinstance(t,tuple) else e.get(t,t)
def contains(a,u):return a==u or isinstance(a,tuple) and (contains(a[0],u) or contains(a[1],u))
def admissible(u,a):return u==T or contains(a,u)
def size(t):return 1 if not isinstance(t,tuple) else 1+size(t[0])+size(t[1])
base={2,3,6,8,9,12,13,15,16,17,25,39,40,59}
@cache
def guards(n):
    names,_,body=rows[n]
    if n in base:return frozenset()
    if n==0:return frozenset({('v1','v2')})
    def walk(t):
        if t[0]=='T_mp':
            assert len(t)==5 and t[1:3]==('_','_')
            return walk(t[3])|walk(t[4])
        assert t[0].startswith('cd_')
        j=int(t[0][3:]); assert j<n
        args=[term(x,{v:v for v in names}) for x in t[1:]]
        assert len(args)==len(rows[j][0])
        env=dict(zip(rows[j][0],args)); out=set()
        for u,a in guards(j):
            su,sa=subst(u,env),subst(a,env)
            if not admissible(su,sa):out.add((su,sa))
        return out
    return frozenset(walk(body))
# First B independently; then use its unconditional result as the source builder does.
b_guard=guards(91); assert not b_guard,b_guard
base.add(91); guards.cache_clear()
stats=[{'id':n,'guards':len(guards(n)),'guard_tree_nodes':sum(size(u)+size(a) for u,a in guards(n))} for n in rows]
assert not guards(106)
r={'scope':'Inert symbolic dominance-obligation propagation, not a Lean proof or rule checker','input':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'lemmas':len(rows),'unconditional_base_ids':sorted(base),'B_remaining_guards':len(b_guard),'S_remaining_guards':len(guards(106)),'statistics':stats,'total_guard_pairs':sum(x['guards'] for x in stats),'max_guard_pairs':max(x['guards'] for x in stats),'total_guard_tree_nodes':sum(x['guard_tree_nodes'] for x in stats)}
Path('/tmp/k215-domrho8-conceptual-survey/guards-result.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items() if k!='statistics'},indent=2))
print('nontrivial',[(x['id'],x['guards']) for x in stats if x['guards']])
