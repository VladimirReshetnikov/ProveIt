import os,re,difflib
imp={}
def imps(m):
    if m not in imp:
        p=m+'.lean'; imp[m]=re.findall(r'^import GowersSzemeredi\.(\S+)',open(p,encoding='utf8').read(),re.M) if os.path.exists(p) else []
    return imp[m]
clo=set(); st=['Proofs18Final']
while st:
    x=st.pop()
    if x in clo: continue
    clo.add(x); st+=imps(x)
def decls(path):
    s=open(path,encoding='utf8').read()
    out=[]
    for p in re.split(r'\n(?=(?:theorem|lemma|def) )',s):
        m=re.match(r'(?:theorem|lemma|def) (\S+)',p)
        if m and p.count('\n')>=12: out.append((m.group(1),p))
    return out
final={}
for f in ['Proofs18FinalClasses','Proofs18FinalStep','Proofs18FinalEnvelopes','Proofs18Final']:
    for n,b in decls(f+'.lean'): final[(f,n)]=b
others=[(m,n,b) for m in clo if not m.startswith('Proofs18Final') for n,b in decls(m+'.lean')]
print(len(clo),'closure modules;',len(others),'candidate decls',flush=True)
norm=lambda t: re.sub(r"[A-Za-z_][\w']*", lambda m: m.group(0) if m.group(0) in ('have','obtain','exact','refine','rw','by','fun','calc') else 'X', t)
on=[(g,m,norm(c)) for g,m,c in others]
res=[]
for (f,n),b in final.items():
    nb=norm(b); L=len(nb); best=(0,None)
    for g,m,nc in on:
        if abs(len(nc)-L)>0.3*L: continue
        sm=difflib.SequenceMatcher(None,nb,nc,autojunk=False)
        if sm.real_quick_ratio()<=best[0] or sm.quick_ratio()<=best[0]: continue
        r=sm.ratio()
        if r>best[0]: best=(r,(g,m))
    res.append((best[0],f,n,b.count('\n'),best[1]))
for r in sorted(res,reverse=True)[:15]: print(f'{r[0]:.2f} {r[1]}.{r[2]} ({r[3]} lines) ~ {r[4]}',flush=True)
