"""Own guarded-template producer. Everything emitted is an ordinary Lean proof."""
import contextlib,io,runpy,json,hashlib,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
original=ROOT/'Computability/BusyBeaver/Research/ZFC/k225-formal/lean217/dominated_rho8_full_certificate.json'
generator=ROOT/'Computability/BusyBeaver/Research/ZFC/k225-formal/generate_domrho8_lean.py'
d=json.loads(original.read_text()); d['nodes']=d['nodes'][:61]
# Keep exactly the bootstrap nodes; remove unrelated input terms only.
used=set()
def termvisit(i):
    if i in used:return
    used.add(i)
    if isinstance(d['term_table'][i],list):
        for j in d['term_table'][i]:termvisit(j)
for n in d['nodes']:
    termvisit(n['term'])
    for f in ('substitution','major_substitution','minor_substitution'):
        for t in n['rule'].get(f,{}).values():termvisit(t)
for i,t in enumerate(d['term_table']):
    if t=='T' or isinstance(t,dict):termvisit(i)
ids={i:j for j,i in enumerate(sorted(used))}
new=[]
for n in d['nodes']:
    r=dict(n['rule'])
    for f in ('substitution','major_substitution','minor_substitution'):
        if f in r:r[f]={v:ids[t] for v,t in r[f].items()}
    new.append(dict(n,term=ids[n['term']],rule=r))
d['nodes']=new;d['term_table']=[[ids[c] for c in d['term_table'][i]] if isinstance(d['term_table'][i],list) else d['term_table'][i] for i in sorted(used)]
(P/'bootstrap.json').write_text(json.dumps(d,separators=(',',':'))+'\n')
s=generator.read_text();s=s.replace('T, N = reduce_certificate(T, N)','T, N = T, N  # Exact61 bootstrap; no schema search/pruning.')
s=s[:s.index('root = N[-1]["term"]')]+'''w("end\\nend SetTheory.BusyBeaver.ZFC.DomRho8\\n")
open(out,"w").write("\\n".join(L))
'''
(P/'bootstrap_renderer.py').write_text(s)
r=subprocess.run([sys.executable,str(P/'bootstrap_renderer.py'),str(P/'bootstrap.json'),str(P/'Bootstrap.lean'),'--no-plan'],capture_output=True,text=True,timeout=10)
(P/'bootstrap-render.log').write_text(r.stdout+r.stderr);assert r.returncode==0
with contextlib.redirect_stdout(io.StringIO()):m=runpy.run_path(str(P/'guards.py'))
rows,guards,imp,term,subst,contains=m['rows'],m['guards'],m['imp'],m['term'],m['subst'],m['contains'];T=m['T'];base=m['base']-{91}
def lean(t):return ('0' if t==T else t) if isinstance(t,str) else '(wim '+lean(t[0])+' '+lean(t[1])+')'
def norm(t):return imp(norm(t[0]),norm(t[1])) if isinstance(t,tuple) else t
def prove_le(u,a,available):
    if u==T:return '(Nat.zero_le _)'
    if u==a:return '(Nat.le_refl _)'
    if (u,a) in available:return available[(u,a)]
    if isinstance(a,tuple):
        if contains(a[0],u):return '(le_l '+lean(a[1])+' '+prove_le(u,a[0],available)+')'
        if contains(a[1],u):return '(le_r '+lean(a[0])+' '+prove_le(u,a[1],available)+')'
    raise ValueError(('unprovedguard',u,a,available))
patterns=[('basisI',('a','a')),('basisK',('a',('b','a'))),('basisP',((('a','b'),'a'),'a')),('basisJ',(('a','b'),((('a','c'),'a'),'b')))]
def match(p,t,e):
    if isinstance(p,str):
        if p in e:return e[p]==t
        e[p]=t;return True
    return isinstance(t,tuple) and match(p[0],t[0],e) and match(p[1],t[1],e)
def basis(t):
    for name,p in patterns:
        env={}
        if match(p,t,env):return '('+name+' h '+' '.join(lean(env[x]) for x in ('a','b','c') if x in env)+')'
    assert isinstance(t,tuple)
    return '(h.mp (basisK h '+lean(t[1])+' '+lean(t[0])+') '+basis(t[1])+')'
L=['''section
variable {T : Nat → Prop} (h : DomImp T)
include h
private theorem basisI (a : Nat) : T (wim a a) := n17 h (sub [a])
private theorem basisK (a b : Nat) : T (wim a (wim b a)) := n60 h (sub [a,b])
private theorem basisP (a b : Nat) : T (wim (wim (wim a b) a) a) := n25 h (sub [a,b])
private theorem basisJ (a b c : Nat) : T (wim (wim a b) (wim (wim (wim a c) a) b)) := n57 h (sub [a,b,c])
''']
used_templates=set()
def use_template(n):
    if n in used_templates:return
    used_templates.add(n)
    if n in base or n==0:return
    def walk(t):
        if t[0]=='T_mp':walk(t[3]);walk(t[4])
        else:use_template(int(t[0][3:]))
    walk(rows[n][2])
use_template(106);use_template(91)
for n,(names,wanted,body) in rows.items():
    if n not in used_templates:continue
    e={v:v for v in names};gs=sorted(guards(n),key=repr);avail={g:'hb'+str(i) for i,g in enumerate(gs)}
    bind=' '.join('(hb'+str(i)+' : '+lean(u)+' ≤ '+lean(a)+')' for i,(u,a) in enumerate(gs))
    def rawterm(t):
        if isinstance(t,str):return T if t=='0' else e[t]
        return (rawterm(t[1]),rawterm(t[2]))
    def walk(t):
        if t[0]=='T_mp':
            mi,miout=walk(t[3]);ma,maout=walk(t[4]);
            if maout==T:maout=(T,T)
            assert maout[0]==miout
            return '(h.mp '+ma+' '+mi+')',maout[1]
        j=int(t[0][3:]);args=[term(x,e) for x in t[1:]];en=dict(zip(rows[j][0],args));bs=[]
        for u,a in sorted(guards(j),key=repr):bs.append(prove_le(subst(u,en),subst(a,en),avail))
        pf='(cd'+str(j)+' h '+' '.join(map(lean,args))+(' '+' '.join(bs) if bs else '')+')'
        out=term(rows[j][1],en)
        # Statements may contain truth-zero compositions after parameter instantiation.
        raw=rawterm(rows[j][1]) if False else None
        
        def rawsubst(t):
            if isinstance(t,str):return T if t=='0' else en[t]
            return (rawsubst(t[1]),rawsubst(t[2]))
        if rawsubst(rows[j][1]) != out:
            pf='(show T '+lean(out)+' from by simpa only [wim00] using '+pf+')'
        return pf,out
    if n==0:
        pf='(show T '+lean(term(wanted,e))+' from by simpa only [Code254.rho8] using h.rho8 v2 v3 v0 v1 hb0)'
    elif n in base:pf=basis(term(wanted,e))
    else:pf=walk(body)[0]
    # simp uses only the proved zero alias, never arithmetic unfolding.
    L.append('private theorem cd'+str(n)+' ('+' '.join(names)+' : Nat) '+bind+' :\n    T '+lean(term(wanted,e))+' := by\n  simpa only [wim00] using '+pf+'\n')
L += ['''theorem composition (a b c : Nat) : T (wim (wim a b) (wim (wim b c) (wim a c))) := cd91 h a b c
theorem distribution (a b c : Nat) : T (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) := cd106 h a b c
end
#print axioms composition
#print axioms distribution
end SetTheory.BusyBeaver.ZFC.DomRho8
''']
bootstrap=(P/'Bootstrap.lean').read_text();assert bootstrap.endswith('end\nend SetTheory.BusyBeaver.ZFC.DomRho8\n')
joined='\n'.join(L)
joined=joined.replace('end\n#print axioms composition', (P/'Conclusion.lean').read_text()+'\nend\n#print axioms rho8_all\n#print axioms composition')
source=bootstrap[:-len('end SetTheory.BusyBeaver.ZFC.DomRho8\n')]+'\n'+joined
(P/'Pilot.lean').write_text(source)
print(json.dumps({'bytes':len(source.encode()),'lines':source.count('\n'),'bootstrap_nodes':61,'bootstrap_input_terms':len(d['term_table']),'templates':len(rows),'guarded_templates':sum(bool(guards(n)) for n in rows),'sha256':hashlib.sha256(source.encode()).hexdigest()},indent=2))
