import os,re,difflib,sys,collections
GS=r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi'
used=set()
for l in open(sys.argv[1],encoding='utf8'):
    m,n,a,b=l.split(); used.add(n.split('.')[-1])
bodies=[]
for f in os.listdir(GS):
    if not f.endswith('.lean') or 'Audit' in f: continue
    s=open(os.path.join(GS,f),encoding='utf8').read()
    for p in re.split(r'\n(?=(?:theorem|lemma|def) )',s):
        m=re.match(r'(?:theorem|lemma|def) (\S+)',p)
        if m and m.group(1).split('.')[-1] in used and p.count('\n')>=12:
            bodies.append((f[:-5],m.group(1),p))
print(len(bodies),'used decls >= 12 lines',flush=True)
norm=lambda t: re.sub(r"[A-Za-z_][\w']*", lambda m: m.group(0) if m.group(0) in ('have','obtain','exact','refine','rw','by','fun','calc') else 'X', t)
nb=[(f,n,norm(b),b.count('\n')) for f,n,b in bodies]
nb.sort(key=lambda x:len(x[2]))
res=[]
for i in range(len(nb)):
    fi,ni,bi,li=nb[i]
    for j in range(i+1,len(nb)):
        fj,nj,bj,lj=nb[j]
        if len(bj)>1.25*len(bi): break
        sm=difflib.SequenceMatcher(None,bi,bj,autojunk=False)
        if sm.real_quick_ratio()<0.9 or sm.quick_ratio()<0.9: continue
        r=sm.ratio()
        if r>=0.9: res.append((r,li,lj,f'{fi}.{ni}',f'{fj}.{nj}'))
res.sort(reverse=True)
for r in res[:40]: print(f'{r[0]:.2f} {r[1]:3}/{r[2]:3} {r[3]}  ~  {r[4]}',flush=True)
print(len(res),'pairs >= 0.90')
