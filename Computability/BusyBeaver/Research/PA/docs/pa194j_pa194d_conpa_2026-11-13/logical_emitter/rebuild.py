#!/usr/bin/env python3
"""Rebuild PA194D from pinned PA194, and prove its finite source invariant.

Standard library only; no network, compiler package, or proof assistant needed.
This is an executable finite certificate, not a Lean/Rocq kernel theorem.
"""
from pathlib import Path
import hashlib,json,re,sys

ROOT=Path(__file__).resolve().parent
INPUT=ROOT/'inputs';OUT=ROOT/'machine';EVIDENCE=ROOT/'evidence'
NAME='pa194d'
START,HALT=74,254
PHYSICAL=[6,2,0,4,3,7,8,5,1]
EXPECTED_NATIVE='bc8ab6c58badd137535938c9810e39d19152c49dd2eb26ef4ea07dbcf3157231'

def digest(data):return hashlib.sha256(data).hexdigest()
def dump(path,data):path.write_text(json.dumps(data,indent=2)+'\n')
def parse(path):
    rows={}
    for line in path.read_text().splitlines():
        if not line.strip():continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        assert (q,b) not in rows and b in(0,1) and w in(0,1) and d in('L','R')
        rows[q,b]=(w,d,n)
    return rows
def tabletext(rows):
    return ''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(rows.items()))
def original_nodes():
    nodes={}
    for line in (INPUT/'Program.lean').read_text().splitlines():
        m=re.match(r'def (\w+) : Tree := \.node (.*)',line)
        if not m:continue
        tokens=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2])
        children=[name if name else ('leaf',op,int(arg) if arg else None)for op,arg,name in tokens]
        assert len(children)==2
        nodes[m[1]]=tuple(children)
    return nodes
def grammar():
    g=json.loads((INPUT/'pa194.grammar.json').read_text())
    def expand(x):
        if isinstance(x,list):return tuple(x)
        if x in g['rules']:return tuple(expand(y)for y in g['rules'][x])
        return x
    return expand(g['root'])
def replace_final_break(t):
    if t==('leaf','breakTo',1):return ('leaf','dec',4),1
    if isinstance(t,tuple) and len(t)==2:
        a,ca=replace_final_break(t[0]);b,cb=replace_final_break(t[1]);return (a,b),ca+cb
    return t,0
def source(nodes,ax):
    sites=[]
    def walk(t,p):
        if isinstance(t,str):return walk(ax if t=='x67' else nodes[t],p)
        if t[0]=='leaf':sites.append([p,t[1],t[2]]);return
        walk(t[0],p+'0');walk(t[1],p+'1')
    walk('node172','')
    bypath={p:i for i,(p,op,arg)in enumerate(sites)}
    assert len(bypath)==len(sites)
    def locate(p):
        if p in bypath:return bypath[p]
        for i,(q,op,arg)in enumerate(sites):
            if q.startswith(p)or(p.startswith(q)and'1'not in p[len(q):]):return i
        raise AssertionError(('unresolved address',p))
    def after(p):
        i=p.rfind('0');assert i>=0;return locate(p[:i]+'1')
    def cut(p,bit,k):
        for i in range(len(p)-1,-1,-1):
            if p[i]==bit:
                k-=1
                if not k:return p[:i]
        raise AssertionError(('invalid structured jump',p,bit,k))
    instructions=[]
    for p,op,arg in sites:
        if op=='inc':z=['inc',arg,after(p)]
        elif op=='dec':z=['dec',arg,after(cut(p,'0',1)),after(p)]
        elif op=='breakTo':z=['jump',after(cut(p,'0',arg))]
        elif op=='continueTo':z=['jump',locate(cut(p,'1',arg))]
        elif op=='halt':z=['halt']
        else:raise AssertionError(op)
        instructions.append(z)
    return sites,instructions

def succ(code,pc,mask):
    z=code[pc]
    if z[0]=='jump':return [(z[1],mask)]
    if z[0]=='inc':return [(z[2],mask|(1<<z[1]))]
    if z[0]=='dec':
        bit=1<<z[1]
        return [(z[3],mask&~bit),(z[3],mask)]if mask&bit else[(z[2],mask)]
    assert z[0]=='halt';return []
def closure(code):
    seen={(25,1)};todo=list(seen)
    for pc,m in todo:
        for x in succ(code,pc,m):
            assert 0<=x[0]<len(code) and 0<=x[1]<512
            if x not in seen:seen.add(x);todo.append(x)
    return seen

def load_grammar(path):
    g=json.loads(path.read_text())
    def go(x):
        if isinstance(x,list):return tuple(x)
        return tuple(go(y)for y in g['rules'][x])if x in g['rules']else x
    return go(g['root'])
INC=('leaf','inc',1);BREAK=('leaf','breakTo',1)
def node(t):return isinstance(t,tuple)and len(t)==2
def normalize(t):
    if t=='node60':return INC,INC
    if t=='node61':return(INC,INC),(INC,INC)
    return tuple(normalize(x)for x in t)if node(t)else t
def word(t):return word(t[0])+word(t[1])if node(t)else[t]
def changed_last(t,leaf):
    if t==('leaf','dec',4)or t==BREAK:return leaf
    return tuple(changed_last(x,leaf)for x in t)if node(t)else t

def compile_rows(tree):
    rows={k:v for k,v in parse(INPUT/'pa194.native.tm').items()if k[0]<1300}
    assert len(rows)==268
    rows.update({(164,1):(1,'R',130),(38,0):(0,'R',11),(38,1):(1,'R',122),
        (214,0):(0,'R',312),(214,1):(1,'R',20),(312,0):(0,'R',188),(27,1):(1,'R',21)})
    macros={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,
        'node72':69,'node75':213,'node142':194,'node150':221,INC:61,
        (INC,INC):99,((INC,INC),(INC,INC)):190,('leaf','dec',4):144}
    index={}
    def state(t):
        if t in macros:return macros[t]
        if t in index:return index[t]
        assert node(t),t
        q=2000+len(index);index[t]=q
        for bit,child in enumerate(t):
            rows[q,bit]=(0,'L',302)if child==BREAK else(bit,'R',state(child))
        return q
    rows[101,1]=(1,'R',state(tree));assert len(index)==69
    return rows

def quotient(raw,folds):
    aliases={a:b for a,b,acts in folds};actions={b:acts for a,b,acts in folds}
    assert len({q for a,b,acts in folds for q in(a,b)})==2*len(folds)
    child={}
    for(q,bit),oldact in raw.items():
        if q in aliases:continue
        w,d,n=actions[q][bit]if q in actions else oldact
        d=('R'if d else'L')if isinstance(d,bool)else d
        child[q,bit]=(w,d,aliases.get(n,n))
    return child,aliases

def check_folds(raw,child,aliases,folds):
    incoming={}
    for(q,bit),(w,d,n)in raw.items():incoming.setdefault(n,set()).add((w,d))
    cases=[]
    for a,b,acts in folds:
        assert a!=START and b!=START
        assert incoming[a]=={(0,'R')}and incoming[b]=={(1,'R')}
        for old,history in((a,0),(b,1)):
            for bit in(0,1):
                w,d,n=raw[old,bit];want=(aliases.get(n,n),1 if d=='R'else-1,{-1:history,0:w})
                q,head,tape=b,0,{-1:history,0:bit};trace=[]
                for k in range(1,21):
                    assert head in(-1,0)
                    w,d,q=child[q,tape[head]];tape[head]=w;head+=1 if d=='R'else-1
                    trace.append([q,head,tape[-1],tape[0]])
                    if(q,head,tape)==want:break
                else:raise AssertionError(('failed simultaneous fold',old,bit))
                cases.append({'old':old,'history':history,'bit':bit,'steps':k,'trace':trace})
    return cases

def build():
    assert __debug__ and not sys.flags.optimize,'Run without -O.'
    OUT.mkdir(exist_ok=True);EVIDENCE.mkdir(exist_ok=True)
    assert digest((INPUT/'pa194.native.tm').read_bytes())=='e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
    winner=normalize(load_grammar(INPUT/'winner.grammar.json'))
    oldshape=normalize(grammar());oldword=word(oldshape)
    semantic=json.loads((INPUT/'separateD.word.json').read_text())
    newword=[tuple(x)if isinstance(x,list)else x for x in semantic['node_word']]
    assert len(newword)==len(oldword)==190
    assert[(i,a,b)for i,(a,b)in enumerate(zip(oldword,newword))if a!=b]==[
        (121,'node70','node55'),(122,'node70','node55'),(123,'node70','node55')]
    assert newword[-1]==BREAK
    newword[-1]=('leaf','dec',4);assert word(winner)==newword
    # Transport reassociation against the original accepted association.
    it=iter(newword)
    def substitute(t):return tuple(substitute(x)for x in t)if node(t)else next(it)
    reference=substitute(oldshape);assert next(it,None)is None
    nodes=original_nodes();nodes['node163']=('node6','node147')
    nodes['node170']=(('node36',('node167','node145')),'node57')
    oldsites,old=source(nodes,changed_last(winner,BREAK))
    nodes['node22']=(('leaf','dec',8),('leaf','dec',6))
    sites,new=source(nodes,winner);reference_sites,reference_code=source(nodes,reference)
    assert new==reference_code,'Reassociation changed a structured successor.'
    assert len(new)==len(old)==3649
    changes=[i for i in range(len(new))if old[i]!=new[i]];assert changes==[26,3553]
    assert new[26]==['dec',6,34,27]and new[3553]==['dec',4,3637,3554]
    r0,r1=closure(old),closure(new);assert r0==r1 and len(r0)==263244
    assert(25,1)in r0 and all(succ(old,pc,m)==succ(new,pc,m)for pc,m in r0)
    assert all(x in r0 for pc,m in r0 for x in succ(old,pc,m))
    masks={i:sorted(m for pc,m in r0 if pc==i)for i in changes}
    assert all(not m>>new[i][1]&1 for i in changes for m in masks[i])
    raw=compile_rows(winner);folds=json.loads((INPUT/'nine_folds.json').read_text())
    assert len(folds)==9;rows,aliases=quotient(raw,folds)
    cases=check_folds(raw,rows,aliases,folds);assert len(cases)==36
    native=tabletext(rows);assert digest(native.encode())==EXPECTED_NATIVE
    controls={q for q,b in rows};assert len(controls)==194 and len(rows)==388
    assert {n for w,d,n in rows.values()}-controls=={254}
    order=[START];index={START:0}
    for q in order:
        for bit in(0,1):
            n=rows[q,bit][2]
            if n!=HALT and n not in index:index[n]=len(order);order.append(n)
    assert len(order)==194
    dense={(index[q],b):(w,d,194 if n==HALT else index[n])for(q,b),(w,d,n)in rows.items()}
    (OUT/(NAME+'.native.tm')).write_text(native);(OUT/(NAME+'.tm')).write_text(tabletext(dense))
    (OUT/'unfolded203.native.tm').write_text(tabletext(raw))
    for suffix,data in[('sites',sites),('instructions',new),('labels',order+[HALT])]:dump(OUT/(NAME+'.'+suffix+'.json'),data)
    dump(EVIDENCE/'fold_cases.json',cases)
    dump(EVIDENCE/'source_binding.json',{'macro_tokens':190,'logical_copy_changes':[121,122,123],
        'copy_before':'A','copy_after':'D','closing_zero_register':4,
        'complete_resolved_graph_equal_to_original_shape_with_same_word':True,
        'source_sites':3649,'zero_source_changes':changes})
    dump(EVIDENCE/'zero_invariant.json',{'pairs':len(r0),'same_closure':True,'same_successors':True,
        'closed':True,'seed':[25,1],'masks':masks,
        'sha256':digest(json.dumps(sorted(r0),separators=(',',':')).encode())})
    receipt={'name':NAME,'fixed_states':134,'raw_readers':69,'simultaneous_folds':9,
        'working_states':194,'rows':388,'local_cases':36,'max_local_steps':max(x['steps']for x in cases),
        'source_sites':3649,'source_contracts':4751,'native_sha256':digest(native.encode()),
        'dense_sha256':digest(tabletext(dense).encode()),'kernel_checked':False,
        'proof_scope':'Finite construction, all-tape contextual quotient, source reassociation and zero-test invariant. The Gamma(D) logical calibration is a separate mathematical argument.'}
    dump(EVIDENCE/'build_receipt.json',receipt);return receipt
if __name__=='__main__':print(json.dumps(build(),indent=2))
