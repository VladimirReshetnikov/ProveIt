#!/usr/bin/env python3
"""Independent PA195S8 source, table, local quotient, oracle-premise and startup audit.

Usage: independent_audit_scanner8.py SCANNER8_DIR PA195_REFERENCE_DIR [OUTPUT_DIR]
Uses only the Python standard library; no candidate compiler/runtime imports.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import ast, hashlib, json, re, sys

if len(sys.argv)<3:raise SystemExit(__doc__)
BASE = Path(sys.argv[2])
SOURCE = Path(sys.argv[1])
OUT = Path(sys.argv[3]) if len(sys.argv)>3 else Path(__file__).resolve().parent
OUT.mkdir(exist_ok=True)
PREFIX = OUT/'pa195_scanner8'
for suffix,name in [('.json','grammar.json'),('.folds.json','folds.json'),('.native.tm','pa195_scanner8.native.tm')]:
    PREFIX.with_suffix(suffix).write_bytes((SOURCE/name).read_bytes())

def require(ok, msg):
    if not ok: raise ValueError(msg)

def read_table(p):
    out={}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,r,w,d,n=line.split();q,r,w,n=map(int,(q,r,w,n))
        require(r in (0,1) and w in (0,1) and d in ('L','R'),'malformed binary row')
        require((q,r) not in out,'duplicate transition')
        out[q,r]=(w,1 if d=='R' else -1,n)
    return out

# Independently parse the small Tree fragment of the pinned Lean source.
defs={}
for line in (BASE/'vendor/reference/PA196/Program.lean').read_text().splitlines():
    m=re.fullmatch(r'def (\w+) : Tree := (.+)',line)
    if m:defs[m[1]]=m[2]

def parse_tree(text):
    toks=re.findall(r'\.\w+|\w+|[()]',text);k=0
    def take():
        nonlocal k
        t=toks[k];k+=1;return t
    def op():
        t=take()
        if t=='(':
            v=op();require(take()==')','operation parenthesis');return v
        require(t in ('.inc','.dec','.continueTo','.breakTo','.halt'),'operation token')
        return ('L',t[1:],None if t=='.halt' else int(take()))
    def tree():
        t=take()
        if t=='(':
            v=tree();require(take()==')','tree parenthesis');return v
        if t=='.node':return ('N',tree(),tree())
        if t=='.leaf':return op()
        require(t in defs,'tree reference '+t);return t
    v=tree();require(k==len(toks),'trailing source token');return v
rawdefs={name:parse_tree(body) for name,body in defs.items()}

def read_grammar(path):
    doc=json.loads(path.read_text());rules=doc['rules']
    @lru_cache(None)
    def rec(name):
        if name not in rules:return name
        value=rules[name];require(len(value)==2,'grammar arity')
        return ('N',convert(value[0]),convert(value[1]))
    def convert(value):
        if isinstance(value,list):
            require(len(value)==3 and value[0]=='leaf','grammar leaf')
            return ('L',value[1],value[2])
        return rec(value)
    return rec(doc['root'])

grammar=read_grammar(PREFIX.with_suffix('.json'))
@lru_cache(None)
def expand(t):
    if isinstance(t,str):return expand(grammar if t=='x67' else rawdefs[t])
    if t[0]=='L':return t
    return ('N',expand(t[1]),expand(t[2]))
full=expand('node172')
@lru_cache(None)
def size(t):return 1 if t[0]=='L' else size(t[1])+size(t[2])
N=size(full);sites=[];cfg=[]
def walk(t,lo,path,breaks,continues):
    if t[0]=='L':
        _,op,arg=t;sites.append((path,op,arg));nxt=(lo+1)%N
        if op=='inc':instruction=['inc',arg,nxt]
        elif op=='dec':instruction=['dec',arg,breaks[0],nxt]
        elif op=='breakTo':instruction=['jump',breaks[arg-1]]
        elif op=='continueTo':instruction=['jump',continues[arg-1]]
        else:instruction=['halt']
        cfg.append(instruction);return
    hi=(lo+size(t))%N;mid=lo+size(t[1])
    walk(t[1],lo,path+'0',(hi,)+breaks,continues)
    walk(t[2],mid,path+'1',breaks,(lo,)+continues)
walk(full,0,'',(),())
reference=json.loads((BASE/'source.json').read_text())
require(len(sites)==len(reference)==3700,'source size')
require([(op,arg) for path,op,arg in sites]==[(x['op'],x['arg']) for x in reference],'ordered source instructions')
require(cfg==[x['instruction'] for x in reference],'independent structural CFG changed')
require(sites[25][0]=='100000','seed path changed')

# Preserve the exact emitter word, expanding only its two predefined increments.
names={'node49':'push','node55':'copyD','node58':'copyH','node70':'copyA','node65':'cons','node72':'readH','node75':'readDCons','node142':'copyGuard','node150':'compareGuard'}
def word(t):
    if isinstance(t,str):return ['incT']*({'node60':2,'node61':4}[t]) if t in ('node60','node61') else [names[t]]
    if t[0]=='N':return word(t[1])+word(t[2])
    return ['incT' if t==('L','inc',1) else 'close']
require(word(grammar)==json.loads((BASE/'emitter_tokens.json').read_text()),'emitter token sequence changed')

# Compile read-only binary choices independently from the pinned inherited table.
labels=ast.literal_eval(re.search(r'def labels : List Nat := (\[[^\n]+\])',(BASE/'vendor/reference/PA196/Conjugacy.lean').read_text())[1])
inherited=read_table(BASE/'vendor/reference/data/pa196.tm')
raw={(labels[q],r):(w,d,labels[n]) for (q,r),(w,d,n) in inherited.items() if labels[q]<1300}
raw[34,0]=(0,-1,1999)
raw[1999,0]=(0,-1,75)
raw[1999,1]=(1,-1,2)
inc=('L','inc',1);pair=('N',inc,inc)
macros={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,inc:61,'node60':99,'node61':190,pair:99,('N',pair,pair):190}
allocated={}
def allocate(t):
    if t in macros:return macros[t]
    if t in allocated:return allocated[t]
    require(isinstance(t,tuple) and t[0]=='N','unexpected allocation')
    q=2000+len(allocated);allocated[t]=q
    for bit,child in enumerate(t[1:]):
        raw[q,bit]=(0,-1,302) if child==('L','breakTo',1) else (bit,1,allocate(child))
    return q
raw[101,1]=(1,1,allocate(grammar))
require(raw==read_table(SOURCE/'unfolded203.native.tm'),'unfolded203 table differs')
source_record=json.loads((SOURCE/'source.json').read_text())
require(source_record==[{'ordinal':i,'path':path,'op':op,'arg':arg,'instruction':cfg[i]} for i,(path,op,arg) in enumerate(sites)],'published full source record differs')
folds=json.loads(PREFIX.with_suffix('.folds.json').read_text())
pairs=[(a,b) for a,b,acts in folds]
flat=[q for pair in pairs for q in pair]
require(len(set(flat))==len(flat),'overlapping aliases')
require(74 not in flat and 254 not in flat,'folds start or halt')
alias={a:b for a,b in pairs}
def project(q):return alias.get(q,q)
replacements={b:[(w,1 if d else -1,n) for w,d,n in acts] for a,b,acts in folds}
quotient={}
for (q,bit),action in raw.items():
    if q in alias:continue
    w,d,n=replacements[q][bit] if q in replacements else action
    quotient[q,bit]=(w,d,project(n))
literal=read_table(PREFIX.with_suffix('.native.tm'))
require(quotient==literal,'literal native table differs from independent compilation')
rawstates={q for q,_ in raw};states={q for q,_ in literal}
require(set(literal)=={(q,r) for q in states for r in (0,1)},'incomplete domain')
require(all(n in states|{254} for w,d,n in literal.values()),'unknown successor')
require(254 not in states,'halt counted as working state')

# Each folded parent control has one fixed incoming left-neighbor bit.
history={q:p for a,b in pairs for q,p in ((a,0),(b,1))}
incoming=[]
for (q,r),(w,d,n) in raw.items():
    if n in history:
        require((w,d)==(history[n],1),'incoming-history premise failed')
        incoming.append((q,r,w,d,n))
require(set(history)<={n for q,r,w,d,n in incoming},'folded source has no incoming')
traces=[]
for q,pbit in sorted(history.items()):
    for read in (0,1):
        w,d,n=raw[q,read];target=(project(n),d,4*pbit+w)
        state=project(q);head=0;tape=4*pbit+read;trace=[];seen=set()
        while True:
            require(head in (-1,0),'detour accessed cell outside {-1,0}')
            key=(state,head,tape);require(key not in seen,'detour loops');seen.add(key)
            oldbit=(tape//4)%2 if head==-1 else tape%2
            ww,dd,nn=literal[state,oldbit]
            trace.append([state,head,oldbit,ww,'R' if dd==1 else 'L',nn])
            tape=(tape%4+4*ww) if head==-1 else (tape//4*4+ww)
            state=nn;head+=dd
            if (state,head,tape)==target:break
        traces.append({'parent_state':q,'history_bit':pbit,'read':read,'duration':len(trace),'steps':trace})
for (q,r),(w,d,n) in raw.items():
    if q not in history:require(literal[q,r]==(w,d,project(n)),'ordinary row fails to commute')
published_cert=json.loads((SOURCE/'local_fold_certificate.json').read_text())
require(published_cert['local_cases']==len(traces),'published local case count')
for t,saved in zip(traces,published_cert['local_traces']):
    require((t['parent_state'],t['history_bit'],t['read'],t['duration'],t['steps'])==(saved['raw_state'],saved['left_bit'],saved['read_bit'],saved['duration'],saved['steps']),'published local trace differs')
require(len(published_cert['local_traces'])==len(traces),'published trace length')
require(published_cert['incoming_rows']==[list(x)+[history[x[-1]]] for x in incoming],'published incoming-row certificate')

reachable={74};todo=[74]
for q in todo:
    for r in (0,1):
        n=literal[q,r][2]
        if n!=254 and n not in reachable:reachable.add(n);todo.append(n)
require(reachable==states,'unreachable working controls')
# Literal dense/native conjugacy, separately from compilation.
dense=read_table(SOURCE/'pa195_scanner8.tm')
dense_labels=json.loads((SOURCE/'labels.json').read_text())
require(len(dense_labels)==len(set(dense_labels))==196 and dense_labels[0]==74 and dense_labels[-1]==254,'dense labels')
require(set(dense)=={(q,r) for q in range(195) for r in (0,1)},'dense domain')
require({(dense_labels[q],r):(w,d,dense_labels[n]) for (q,r),(w,d,n) in dense.items()}==literal,'dense/native conjugacy')
# Check inherited register-engine oracle premises literally against pinned Lean.
native_lean=(BASE.parent/'reference_sources/M6/Native.lean').read_text()
box=ast.literal_eval(re.search(r'def boxStates : List Nat :=\s*(\[[^\]]+\])',native_lean)[1])
old={(labels[q],r):(w,d,labels[n]) for (q,r),(w,d,n) in inherited.items()}
require(len(box)==23 and all(literal[q,r]==old[q,r] for q in box for r in (0,1)),'protected oracle rows changed')
ref230=(BASE.parent/'reference_sources/M6/Reference230.lean').read_text().split('def table230')[1]
rr=re.findall(r'\(some \((true|false), (true|false), (\d+)\), some \((true|false), (true|false), (\d+)\)\)',ref230)
require(len(rr)==230,'Reference230 row count')
reference230={(q,r):(int(row[3*r]=='true'),1 if row[3*r+1]=='true' else -1,int(row[3*r+2])) for q,row in enumerate(rr) for r in (0,1)}
required=[(q,r) for q in box for r in (0,1) if (q,r) not in [(113,0),(198,0)]]
require(len(required)==44 and all(literal[k]==reference230[k] for k in required),'Reference230 inherited oracle rows')
require(literal[198,0]==(1,-1,40),'Native append-one tail')
# Independently form the complete target tape from the register-file definition.
physical=[0,0,0,0,0,0,2,0,0]+[1]*26
want={-3,-2};cursor=46;want.add(cursor);cursor+=1
for value in physical:
    cursor+=1;want.update(range(cursor,cursor+value+1));cursor+=value+1
startup_results={}
for tag,table in [('raw203',raw),('folded195',literal)]:
    state,head,ones=74,0,set()
    for tick in range(59164):
        w,d,state=table[state,int(head in ones)]
        (ones.add if w else ones.discard)(head);head+=d
    require((state,head,ones)==(84,-2,want),tag+' exact blank startup')
    startup_results[tag]={'literal_steps':59164,'native_state':state,'head':head,'one_cells':len(ones),'exact_complete_tape':True}
# A different dense, finite-array representation gives the same complete result.
T=59164;array=bytearray(2*T+1);head=T;state=0
for tick in range(T):
    w,d,state=dense[state,array[head]];array[head]=w;head+=d
require((dense_labels[state],head-T,{i-T for i,x in enumerate(array) if x})==(84,-2,want),'dense bytearray startup')
startup_results['dense_bytearray']={'literal_steps':T,'dense_state':state,'native_state':dense_labels[state],'head':head-T,'exact_complete_tape':True}
expected_startup={'literal_steps':59164,'native_state':84,'absolute_head':-2,'header_gap':48,'physical_register_file':physical,'complete_one_positions':sorted(want),'outside_tape_all_zero':True}
require(json.loads((SOURCE/'startup_certificate.json').read_text())==expected_startup,'published startup certificate differs')
maxzero=max(max(map(len,path.split('1'))) for path,op,arg in sites)
receipt={
 'candidate_prefix':str(PREFIX),'native_sha256':hashlib.sha256(PREFIX.with_suffix('.native.tm').read_bytes()).hexdigest(),
 'independent_parser':True,'independent_structural_cfg':True,'independent_compiler':True,'independent_two_cell_executor':True,
 'primitive_sites':N,'identical_ordinal_cfg_to_pa195':True,'emitter_tokens':len(word(grammar)),
 'same_emitter_word_as_pa195':True,'seed_path':sites[25][0],
 'max_path_length':max(len(path) for path,op,arg in sites),'max_source_zero_run':maxzero,
 'raw_controls':len(rawstates),'AX_allocations':len(allocated),'folds':pairs,'incoming_rows':len(incoming),
 'new_controls':len(states),'binary_rows':len(literal),'graph_reachable':len(reachable),
 'two_cell_cases':len(traces),'duration_distribution':dict(Counter(t['duration'] for t in traces)),
 'all_unmodified_rows_commute':True,'all_detours_stay_on_two_cells':True,
 'dense_sha256':hashlib.sha256((SOURCE/'pa195_scanner8.tm').read_bytes()).hexdigest(),
 'dense_native_conjugacy':True,'scanner_patch':[[34,0,0,'L',1999],[1999,0,0,'L',75],[1999,1,1,'L',2]],
 'protected_box_states':box,'all_46_protected_rows_unchanged':True,'native_box_theorem_required_rows':45,
 'blank_startup':startup_results,
 'new_endpoint_kernel_checked':False,
 'runtime_contracts_checked_by_this_script':False,
 'warning':'This independent source, quotient, literal oracle-premise and startup audit is not a new kernel theorem. Full symbolic primitive runtime contracts are a separate obligation.'
}
PREFIX.with_suffix('.independent_audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
PREFIX.with_suffix('.independent_traces.json').write_text(json.dumps(traces,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
