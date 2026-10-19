"""Small exact model of the frozen routed245 grammar inputs."""
import json,os
from pathlib import Path
from functools import cache

BASE = Path(os.environ.get('ZFC245_PACKAGE',str(Path(__file__).resolve().parents[1] / 'packages/zfc245-proof-20261018')))

def load(path=None):
    data = json.loads(Path(path or BASE/'grammar.json').read_text())
    rules = {w:(a,b) for w,a,b in data['rules']}
    lines=(BASE/'inputs/state_reduction/route-grammar.txt').read_text().splitlines()
    n,nr,na=map(int,lines[0].split())
    old={w:(w[:int(k)],w[int(k):]) for k,w,q in map(str.split,lines[1:n+1])}
    roots=lines[n+1:n+1+nr]
    allowed={a:int(b) for a,b in map(str.split,lines[n+1+nr:])}
    cl=(BASE/'inputs/state_reduction/route-constraints.txt').read_text().splitlines()
    i=1;groups=[]
    for j in range(int(cl[0])):
        q,b,w,nc=cl[i].split();i+=1;cs=[]
        for k in range(int(nc)):
            p,t=cl[i].split();i+=1;cs.append((p,t))
        groups.append((int(q),int(b),w,cs))
    ne,orig,na=map(int,cl[i].split());i+=1
    exprs=[row.split() for row in cl[i:i+ne]];i+=ne
    atoms={c:int(a) for c,a in map(str.split,cl[i:i+na])}
    bl=(BASE/'inputs/state_reduction/bootstrap-lock54.txt').read_text().splitlines()
    locks={}
    for w,b,t in map(str.split,bl[1:]):
        locks.setdefault(w,[None,None])[int(b)]=t
    for w in locks:
        if w not in roots: roots.append(w)
    return data,rules,old,roots,allowed,groups,exprs,orig,atoms,locks

def properties(rules,old,exprs,orig,atoms):
    def join(a,b):
        return (1+a[0],max(1+a[0],a[1],b[1]),1+max(a[2],b[2]))
    @cache
    def wprop(w):
        if len(w)==1: return eprop(atoms[w])
        a,b=rules.get(w,old.get(w))
        return join(wprop(a),wprop(b))
    @cache
    def eprop(i):
        e=exprs[i]
        if e[0]=='L': return (0,0,0)
        if e[0]=='W': return wprop(e[1])
        return join(eprop(int(e[1])),eprop(int(e[2])))
    return eprop(orig),wprop,eprop

def resume(data,path):
    Path(path).write_text(str(len(data['rules']))+'\n'+'\n'.join(str(len(a))+' '+w for w,a,b in data['rules'])+'\n'+str(len(data['routes']))+'\n'+'\n'.join(r['word'] for r in data['routes'])+'\n')

if __name__=='__main__':
    data,g,old,roots,allowed,groups,exprs,orig,atoms,locks=load()
    p,wp,ep=properties(g,old,exprs,orig,atoms)
    print('Complete bounds',p)
    print('Locked words:',sorted((w,wp(w)) for w in locks))
    print('Atoms:',sorted((c,ep(a)) for c,a in atoms.items()))
