#!/usr/bin/env python3
"""Independent ordinary source/enumerator binding, not a binary runtime proof.

Reads sources as data. Imports no optimizer, emitter, graph checker, or proof
certificate. Every check uses explicit exceptions and also runs under python -O.
See ORDINARY_PROOF.md for the quantified mathematical contracts justified here.
"""
from pathlib import Path
from functools import cache, reduce
import hashlib, itertools, json, re

W=Path(__file__).resolve().parent/'inputs'
OUT=Path(__file__).resolve().parent
LIB=W/'research_sub246/source/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/prog/Dag254.v'
VD=W/'research_sub237_round2/vacuity_reduction'
PIN=W/'research_sub236/intake/zfc236-research-20261019/source/sites_logical.json'

def req(p,m):
    if not p: raise ValueError(m)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def digest(v): return hashlib.sha256(json.dumps(v,separators=(',',':')).encode()).hexdigest()
def freeze(x): return tuple(map(freeze,x)) if isinstance(x,list) else x
def leaf(t): return isinstance(t[0],str)
def seq(ts): return reduce(lambda a,b:(a,b),ts)

def parse_dag(p):
    ns={}
    tags={'ENode':'N','EInc':'I','EDecnz':'D','EBreak':'B','EContinue':'C','EHalt':'H'}
    for line in p.read_text().splitlines():
        m=re.match(r'\s*\| (\d+) => \(([^,]+), ([^)]*)\)',line)
        if m:
            def edge(s):
                xs=s.split();return (tags[xs[0]],*map(int,xs[1:]))
            ns[int(m[1])]=tuple(map(edge,m.group(2,3)))
    req(len(ns)==219,'Literal Dag254 census changed')
    return ns
N=parse_dag(LIB)
@cache
def tree(q):
    def ed(e): return tree(e[1]) if e[0]=='N' else e
    return tuple(map(ed,N[q]))

def graft(q,ax):
    @cache
    def go(n):
        if n==1:return ax
        def ed(e):return go(e[1])if e[0]=='N'else e
        return tuple(map(ed,N[n]))
    return go(q)

@cache
def boundary(t):
    if leaf(t):
        o=t[0];r=t[1]if len(t)>1 else 0
        return (1,0,False)if o=='D'else(r,0,False)if o=='B'else(0,r,False)if o=='C'else(0,0,o=='H')
    a,b=map(boundary,t)
    return max(max(a[0]-1,0),b[0]),max(a[1],max(b[1]-1,0)),a[2]or b[2]

@cache
def leaves(t):
    if leaf(t):return (('',t),)
    return tuple((str(b)+p,e)for b in(0,1)for p,e in leaves(t[b]))

@cache
def graph(t):
    ps=leaves(t);size=len(ps);spans={}
    for i,(p,e)in enumerate(ps):
        for k in range(len(p)+1):
            u=p[:k]
            if u not in spans:spans[u]=[i,i+1]
            else:spans[u][1]=i+1
    def jump(p,bit,n):
        xs=[i for i,b in enumerate(p)if b==bit]
        if n>len(xs):return ('break'if bit=='0'else 'continue',n-len(xs))
        if n==0:return spans[p][1 if bit=='0'else 0]
        return spans[p[:xs[-n]]][1 if bit=='0'else 0]
    ans=[]
    for i,(p,e)in enumerate(ps):
        o=e[0];r=e[1]if len(e)>1 else 0
        req(o in ('I','D','B','C','H'),'Unknown primitive operation')
        req((o=='H'and len(e)==1)or(o!='H'and len(e)==2 and type(r)is int and r>=0),'Malformed primitive')
        req(o not in ('I','D')or r<9,'Register outside nine-field interface')
        dst=(i+1,)if o=='I'else(jump(p,'0',1),i+1)if o=='D'else(jump(p,'0',r),)if o=='B'else(jump(p,'1',r),)if o=='C'else('halt',)
        ans.append((e,tuple(('break',0)if z==size else z for z in dst)))
    return tuple(ans)

def normalize(g):
    """Sort only uninterrupted increment blocks with no other interior entry.
    Ignore spelling of resolved jumps: their exact targets remain in each row.
    This is a boundary-to-boundary simulation, not instruction-step equality.
    """
    out=list(g);pred={i:set()for i in range(len(g))};changed=[]
    for i,(e,ts)in enumerate(g):
        for q in ts:
            if isinstance(q,int):pred[q].add(i)
    i=0
    while i<len(g):
        if g[i][0][0]!='I':i+=1;continue
        j=i+1
        while j<len(g)and g[j][0][0]=='I'and pred[j]=={j-1}and g[j-1][1]==(j,):j+=1
        es=sorted(g[k][0]for k in range(i,j))
        if es!=[g[k][0]for k in range(i,j)]:changed.append([i,j])
        for k,e in zip(range(i,j),es):out[k]=(e,g[k][1])
        i=j
    return tuple((('J',)if e[0]in('B','C')else e,ts)for e,ts in out),changed

@cache
def fixloops(t):
    if leaf(t):return t
    a,b=map(fixloops,t)
    if leaf(b)and b[0]=='I'and not leaf(a):
        d,tail=a
        if leaf(d)and d[0]=='D'and d[1]!=b[1]and not leaf(tail):
            i,c=tail
            if i==b and c==('C',2):
                req(boundary((a,b))==(0,0,False),'Unclosed copy loop')
                return b,(d,c)
    return a,b

def loop_census(t):
    if leaf(t):return []
    a,b=t;here=[]
    if leaf(b)and b[0]=='I'and not leaf(a):
        d,tail=a
        if leaf(d)and d[0]=='D'and d[1]!=b[1]and not leaf(tail)and tail==(b,('C',2)):
            here=[{'increment_register':b[1],'decrement_register':d[1]}]
    return here+loop_census(a)+loop_census(b)

def from_rows(rows):
    d={}
    for p,o,r in rows:
        req(isinstance(p,str)and set(p)<=set('01'),'Bad path')
        z=d
        for b in p:z=z.setdefault(b,{})
        req('leaf'not in z,'Duplicate leaf')
        z['leaf']=(o[1:],)if o=='CH'else(o[1:],r)
    def go(z):
        if 'leaf'in z:
            req(len(z)==1,'Prefix collision');return z['leaf']
        req(set(z)=={'0','1'},'Incomplete tree');return go(z['0']),go(z['1'])
    return go(d)

def read_source(p):
    j=json.loads(p.read_text())
    if isinstance(j,list):return from_rows(j),j
    if 'structures'in j:
        ns=j['structures']
        @cache
        def go(q):
            x=ns[q]
            return (x[0][1:],)if isinstance(x[0],str)and x[0]=='CH'else(x[0][1:],x[1])if isinstance(x[0],str)else tuple(map(go,x))
    else:
        ns={int(q):v for q,v in j['nodes'].items()}
        @cache
        def go(q):
            return tuple(go(e[1])if e[0]=='N'else tuple(e)for e in ns[q])
    return go(j['root']),j

# Literal macro interfaces already proved in L2Macros254/L2Axioms254.
MACROS={166:'a',121:'b',168:'c',171:'zero',177:'one',119:'imp',181:'rel',182:'eq',180:'all',218:'not',178:'and',183:'exists',176:'read_b',158:'read_u',208:'move_u',192:'copy_c',131:'gate',211:'restore_c',197:'a_to_b'}
TAIL=[192,131,211,197,131]
def expand(q):
    if q in MACROS:return [q]
    ans=[]
    for e in N[q]:
        req(e[0]=='N','Unexpected primitive in AX decomposition');ans+=expand(e[1])
    return ans
OLD=expand(1)
req(OLD[:4]==[166,121,180,176]and OLD[-5:]==TAIL,'Old AX skeleton')
for m in MACROS:
    req(boundary(tree(m))==(0,0,False),f'Unclosed library macro {m}')

I=lambda a,b:('imp',a,b)
R=lambda a,b:('rel',a,b)
E=lambda a,b:('eq',a,b)
A=lambda a,b:('all',a,b)
NN=lambda a:I(a,1)
C=lambda a,b:NN(I(a,NN(b)))
X=lambda a,b:NN(A(a,NN(b)))
a,b,c,u='a','b','c','u'
GEN=A(a,'h')
ROWS={
 'rho8':I(I(I(c,u),a),I(I(a,c),I(b,c))),
 'rho7':I(E(c,a),I(E(c,b),E(a,b))),
 'rho6':I(X(a,A(a,b)),b),
 'rho5':I(E(c,a),I(R(c,b),R(a,b))),
 'rho4':I(A(a,A(b,c)),A(b,A(a,c))),
 'rho3':I(E(a,b),I(R(c,a),R(c,b))),
 'rho2':I(A(a,I(b,c)),I(A(a,b),A(a,c))),
 'rho1':X(a,E(a,b)),
 'K':I(a,I(b,a)),
 'S':I(I(a,I(b,c)),I(I(a,b),I(a,c))),
 'V':I(a,A(a,a)),
 'symmetry':I(E(a,b),E(b,a))}
BC=X(b,C(A(a,I(R(a,b),C(X(c,C(A(b,I(A(c,I(R(c,b),R(c,a))),R(b,c))),R(c,b))),A(c,I(R(c,a),R(c,b)))))),R(c,b)))
BG=X(c,C(A(a,I(R(a,b),A(b,I(c,X(b,C(c,R(b,c))))))),A(b,I(R(b,c),X(a,c)))))
VR=I(R(a,b),A(c,R(a,b)))
VE=I(E(a,b),A(c,E(a,b)))
VEQ=I(E(a,b),A(E(a,b),E(a,b)))
BOLD=C(C(BC,BG),C(VR,VE))

def sym(word):
    stack=['old_top'];B='h';U=None;events=[]
    req(word[-5:]==TAIL,'Exact gates/cleanup not retained')
    for m in word[:-5]:
        if m in(166,121,168,171,177):stack.append({166:a,121:B,168:c,171:0,177:1}[m])
        elif m in(119,181,182,180,178,183):
            req(len(stack)>=3,'Stack underflow into old_top');y,x=stack.pop(),stack.pop();stack.append({119:I,181:R,182:E,180:A,178:C,183:X}[m](x,y))
        elif m==218:stack[-1]=NN(stack[-1])
        elif m==176:
            req(B=='h','Repeated read_b');B=b;events.append('y')
        elif m==158:
            req(U is None,'Repeated u read');U=u;events.append('u')
        elif m==208:
            req(stack[-1]==0 and U==u,'Destructive u read target not zero');stack[-1]=u;U=None
        else:raise ValueError(f'Unknown AX macro {m}')
    req(stack[0]=='old_top'and U is None,'Unfinished AX/old-top corruption')
    return stack,events
old_stack,old_events=sym(OLD)
req(old_stack==['old_top',GEN]+[ROWS[f'rho{i}']for i in range(8,0,-1)]+[BOLD],'Independent old AX formula mismatch')
req(old_events==['y','u'],'Old parser arity')

# Negative conjunction association/commutation is the only allowed bundle edit.
def conjunction(f):
    if isinstance(f,tuple)and f[0]=='imp'and f[2]==1:
        z=f[1]
        if isinstance(z,tuple)and z[0]=='imp'and isinstance(z[2],tuple)and z[2][0]=='imp'and z[2][2]==1:return z[1],z[2][1]
    return None

def canon(f):
    ab=conjunction(f)
    if ab is not None:
        def children(g):
            cs=conjunction(g)
            return children(cs[0])+children(cs[1])if cs is not None else[canon(g)]
        return ('and_multiset',*sorted(children(f),key=repr))
    return (f[0],canon(f[1]),canon(f[2]))if isinstance(f,tuple)else f

def components(f):
    ab=conjunction(f)
    return components(ab[0])+components(ab[1])if ab is not None else[f]
def remap(f,p):return(f[0],remap(f[1],p),remap(f[2],p))if isinstance(f,tuple)else p.get(f,f)
def row_match(f,keys):
    hits=[]
    for key in keys:
        for vals in itertools.permutations('abc'):
            p=dict(zip('abc',vals))
            if f==remap(ROWS[key],p):hits.append((key,p));break
    req(len(hits)==1,f'Unclassified/ambiguous row: {f}')
    return hits[0]

def match_program(actual,expected,label):
    ag,ac=normalize(graph(actual));eg,ec=normalize(graph(expected))
    req(ag==eg,f'Whole source graph differs: {label}')
    req(sum(e[0]=='H'for e,_ in ag)==1,f'Halt census: {label}')
    return dict(instruction_occurrences=len(ag),guarded_cases=sum(2 if e[0]=='D'else 1 for e,_ in ag),normalized_graph_sha256=digest(ag),increment_blocks_sorted_actual=len(ac),increment_blocks_sorted_reference=len(ec),all_ordered_operations_and_resolved_guards_match=True)

# Base identification is an executable graph comparison, not a hash-only theorem.
req(sha(LIB)=='538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3','Wrong checked library DAG')
req(sha(PIN)=='1ebe9691507b2d3236951a31d6b9a7ef548a2cdf90525cd57051992f8ac2626f','Wrong236 base')
baseline,_=read_source(PIN)
receipt={'status':'PASS_ORDINARY_SOURCE_BINDING','binary_runtime_checked_here':False,'new_Lean_theorem':False,'library':str(LIB.relative_to(W)),'library_sha256':sha(LIB),'baseline':{'file':str(PIN.relative_to(W)),'sha256':sha(PIN),**match_program(baseline,fixloops(tree(0)),'baseline236')},'inherited_closed_loop_rewrites':loop_census(tree(0)),'candidates':[]}
req(len(receipt['inherited_closed_loop_rewrites'])==5,'Unexpected loop census')
provider_root=OUT.parent/'reference_lean'
receipt['reused_provider_source_hashes']={name:sha(provider_root/name)for name in ['Dag254.lean','L2Lib254.lean','L2Macros254.lean','L2Control254.lean','L2Axioms254.lean','L2AxiomsEval254.lean','L2Root254.lean','Enum254.lean','EnumSafeStart254.lean','Code254.lean']}
receipt['provider_build_status']='Existing theorem providers inspected; no dependency-closure rebuild or new Lean theorem in this audit.'


# Surgical variant: change the sole scalar c push inside the exact Eq-vacuity word.
old_eq=[166,121,182,168,166,121,182,180,119]
starts=[i for i in range(len(OLD))if OLD[i:i+len(old_eq)]==old_eq]
req(len(starts)==1,'Ambiguous Eq-vacuity slice')
k=starts[0]
new_eq=[166,121,182,166,121,182,166,121,182,180,119]
newword=OLD[:k]+new_eq+OLD[k+len(old_eq):]
newstack,events=sym(newword)
req(newstack==old_stack[:-1]+[C(C(BC,BG),C(VR,VEQ))],'Surgical formula change not exact')
expected_eq=fixloops(graft(0,seq([tree(m)for m in newword])))
for rel in ['restricted_eq_exact236/minimal_existing_builder/source.json','restricted_eq_exact236/local_closed_rotation/source.json']:
    p=VD/rel;actual,j=read_source(p)
    ent=dict(file=str(p.relative_to(W)),sha256=sha(p),kind='H_eq',AX_extra_read_fields=['y','u'],AX_rows_in_emission_order=['GEN']+[f'rho{i}'for i in range(8,0,-1)],GEN_top_first_position=9,row_count=9,stack_cleanup_nips=10,positive_general_V=False,eq_helper='weq(a,b) -> wal(weq(a,b),weq(a,b))',gate='c != a and c != b',**match_program(actual,expected_eq,rel))
    receipt['candidates'].append(ent)

# Full alternate variants: check source data against the independent row schemas,
# then graft the literal macro word into the checked scheduler and compare all CFG.
for rel,kind,eqkind in [('symmetry_canonical_warm/source.json','H_sym','symmetry'),('omit_equality_deep/source.json','H_7','rho7')]:
    p=VD/rel;actual,j=read_source(p);word=j['word'];stack,events=sym(word)
    req(events==['y'],'Alternate AX must read exactly y, with no u field')
    req(stack[1]==GEN,'GEN must preserve old cache before read_b')
    req(stack[1:-1]==list(map(freeze,j['rows'])),'Metadata rows disagree with literal word')
    req(stack[-1]==freeze(j['bundle']),'Metadata bundle disagrees with literal word')
    keys=['K','S','V',eqkind]+[f'rho{i}'for i in range(1,7)]
    matched=[row_match(f,keys)for f in stack[2:-1]]
    req(sorted(k for k,p in matched)==sorted(keys),'Missing or repeated logical schema')
    req(sorted(map(canon,components(stack[-1])),key=repr)==sorted(map(canon,[BC,BG,VR]),key=repr),'Bundle differs beyond conjunction association/commutation')
    expected=graft(0,seq([tree(m)for m in word]))
    # Generic inputs have pretest copy loops. Their transplanted versions use
    # the explicit terminating replacement, checked below.
    ent=dict(file=str(p.relative_to(W)),sha256=sha(p),kind=kind,AX_extra_read_fields=events,AX_rows_in_emission_order=['GEN']+[k for k,p in matched],row_parameter_permutations=[p for k,p in matched],GEN_top_first_position=11,row_count=11,stack_cleanup_nips=12,positive_V_emission_index=1+[k for k,p in matched].index('V'),gate='c != a and c != b',**match_program(actual,expected,rel))
    receipt['candidates'].append(ent)
    for name in ['symmetry_canonical_warm_repair_z8'if kind=='H_sym'else'omit_equality_deep']:
        p2=W/'research_sub236/alternate_backend'/name/'source.json'
        if p2.exists():
            actual2,j2=read_source(p2)
            receipt['candidates'].append(dict(file=str(p2.relative_to(W)),sha256=sha(p2),kind=kind,AX_extra_read_fields=events,row_count=11,GEN_top_first_position=11,reference=str(p.relative_to(W)),closed_loop_rewrites=loop_census(expected),**match_program(actual2,fixloops(expected),name)))

# Bind any currently present literal-backend surgical source by full graph, too.
for dirname in ['restricted_z8','restricted_local_rotation_z7']:
    p=W/'research_sub236/alternate_backend'/dirname/'source.json'
    if p.exists():
        actual,j=read_source(p)
        receipt['candidates'].append(dict(file=str(p.relative_to(W)),sha256=sha(p),kind='H_eq',AX_extra_read_fields=['y','u'],row_count=9,GEN_top_first_position=9,**match_program(actual,expected_eq,dirname)))

# General scalar-helper variants retain exactly the same parser and proof engine.
# Do not infer the scalar builder from its descriptive name: compare the actual
# complete graph against a reference for its declared constructor/order.
kappa_refs={}
for p in sorted((VD/'kappa_exact236').glob('*/source.json')):
    actual,j=read_source(p);kap=freeze(j['kappa'])
    req(kap[0]in('imp','rel','all','eq')and kap[1:]in(('a','b'),('b','a')),'Unknown kappa constructor')
    op={'imp':119,'rel':181,'all':180,'eq':182}[kap[0]]
    push={'a':166,'b':121}
    middle=[push[kap[1]],push[kap[2]],op]
    kw=OLD[:k]+[166,121,182]+middle+[166,121,182,180,119]+OLD[k+len(old_eq):]
    ks,ke=sym(kw)
    req(ke==['y','u']and ks==old_stack[:-1]+[C(C(BC,BG),C(VR,I(E(a,b),A(kap,E(a,b)))))],'Wrong kappa AX word')
    expected=fixloops(graft(0,seq([tree(m)for m in kw])))
    kappa_refs[p.parent.name]=(kap,expected)
    receipt['candidates'].append(dict(file=str(p.relative_to(W)),sha256=sha(p),kind='H_kappa',kappa=kap,AX_extra_read_fields=ke,row_count=9,GEN_top_first_position=9,**match_program(actual,expected,p.parent.name)))
for name,(kap,expected)in kappa_refs.items():
    p=W/'research_sub236/alternate_backend'/('kappa_'+name)/'source.json'
    if p.exists():
        actual,j=read_source(p)
        receipt['candidates'].append(dict(file=str(p.relative_to(W)),sha256=sha(p),kind='H_kappa',kappa=kap,AX_extra_read_fields=['y','u'],row_count=9,GEN_top_first_position=9,**match_program(actual,expected,p.parent.name)))

# Adversarial controls: a changed arithmetic operation, omitted parser field,
# restored old c binder, and wrong GEN cache cannot inherit this certificate.
negative=[]
def rejects(name,f):
    try:f()
    except ValueError:negative.append({'name':name,'rejected':True})
    else:raise ValueError('Negative control accepted: '+name)
wrong=list(newword);wrong[k+3]=168
rejects('restore_old_c_binder',lambda:req(sym(wrong)[0]==newstack,'Different helper'))
wrong=list(newword);wrong.remove(158)
rejects('omit_required_u_read',lambda:sym(wrong))
rejects('change_GEN_cache_to_b',lambda:req(A(a,b)==GEN,'Wrong cached theorem'))
mutated=list(graph(expected_eq));idx=next(i for i,(e,d)in enumerate(mutated)if e[0]=='D');e,d=mutated[idx];mutated[idx]=(('D',(e[1]+1)%9),d)
rejects('change_decrement_register',lambda:req(normalize(tuple(mutated))[0]==normalize(graph(expected_eq))[0],'Changed arithmetic'))
receipt['negative_controls']=negative
(OUT/'binding_results.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
