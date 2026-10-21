"""Read-only independent checks of guard propagation and template inference shapes."""
import contextlib,io,runpy,json,hashlib
from pathlib import Path
with contextlib.redirect_stdout(io.StringIO()):d=runpy.run_path('/tmp/k215-domrho8-conceptual-survey/guards.py')
rows,term,imp,guards=d['rows'],d['term'],d['imp'],d['guards']; base=d['base']; T=d['T']
pairs=0
for n,(names,wanted,body) in rows.items():
    env={v:v for v in names}
    if n==0 or n in base:continue
    def walk(t):
        global pairs
        if t[0]=='T_mp':
            minor,major=walk(t[3]),walk(t[4]); pairs+=1
            if major==T:major=(T,T)
            assert isinstance(major,tuple) and major[0]==minor,(n,t[0],minor,major)
            return major[1]
        k=int(t[0][3:]); args=[term(x,env) for x in t[1:]]
        return term(rows[k][1],dict(zip(rows[k][0],args)))
    assert walk(body)==term(wanted,env),n
# The 14 logical bases need only I/K/Peirce/cd59 plus theorem weakening by K.
a,b,c='a','b','c'
patterns=[imp(a,a),imp(a,imp(b,a)),imp(imp(imp(a,b),a),a),imp(imp(a,b),imp(imp(imp(a,c),a),b))]
def match(p,t,e):
    if isinstance(p,str):
        if p in e:return e[p]==t
        e[p]=t;return True
    return isinstance(t,tuple) and match(p[0],t[0],e) and match(p[1],t[1],e)
def basis(t):
    if any(match(p,t,{}) for p in patterns):return 0
    assert isinstance(t,tuple),t
    return 1+basis(t[1])
bases={str(n):basis(term(rows[n][1],{v:v for v in rows[n][0]})) for n in sorted(base-{91})}
orig=Path('Computability/BusyBeaver/Research/ZFC/k225-formal/lean217/dominated_rho8_full_certificate.json')
o=json.loads(orig.read_text()); nodes=o['nodes']
def deps(i):
    r=nodes[i]['rule']; out={i}
    for field in ('parent','major','minor'):
        if field in r:out|=deps(r[field])
    return out
seed=set().union(*(deps(o['roots'][n]) for n in ['I','K','P','cd59']))
def fmt(t):return str(t) if not isinstance(t,tuple) else '('+fmt(t[0])+' → '+fmt(t[1])+')'
out={'status':'STATIC_TEMPLATE_AND_GUARD_PASS','scope':'Own syntax checks only; no Lean/Rocq invocation or proof acceptance','template_count':len(rows),'checked_mp_nodes':pairs,'base_weakening_depths':bases,'bootstrap_original_ids':sorted(seed),'bootstrap_count':len(seed),'guards':{str(n):[fmt(u)+' ≤ '+fmt(a) for u,a in guards(n)] for n in rows if guards(n)},'B_guards':len(guards(91)),'S_guards':len(guards(106)),'original_sha256':hashlib.sha256(orig.read_bytes()).hexdigest()}
Path('/tmp/k215-domrho8-conceptual-survey/template-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
