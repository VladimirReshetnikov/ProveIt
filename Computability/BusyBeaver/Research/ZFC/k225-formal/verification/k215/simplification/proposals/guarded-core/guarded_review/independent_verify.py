#!/usr/bin/env python3
"""Independent literal-data verifier; never imports or runs received programs.
All interpreter, graph construction, arithmetic, and path checks are authored here.
Run from any working directory. The audit has no proof-assistant build claim.
"""
import os
if not __debug__ or "PYTHONOPTIMIZE" in os.environ:
    raise SystemExit("Optimized Python is unsupported; unset PYTHONOPTIMIZE and run without -O or -OO.")

from pathlib import Path
import collections
import hashlib
import json
import random
import re
import sys
sys.setrecursionlimit(30000)
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent / 'affine'
PACK = ROOT / 'extracted' / 'Affine_Proof_Cores_and_Transport_2026-10-21'

def readj(p): return json.loads(p.read_text())
def check(ok, msg):
    if not ok: raise AssertionError(msg)
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
    b = p.read_bytes()
    return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def ident(): return [[int(i==j) for j in range(10)] for i in range(10)]
def matrix_ok(m):
    return (len(m)==10 and all(len(r)==10 for r in m) and
            all(type(x) is int and x>=0 for r in m for x in r) and
            m[9]==[0]*9+[1])
def mul(a,b): return [[sum(a[i][k]*b[k][j] for k in range(10)) for j in range(10)] for i in range(10)]
def apply(m,r): return [sum(a*b for a,b in zip(row,r+[1])) for row in m[:9]]
def incmat(incs):
    m=ident()
    for r,n in incs:
        check(type(r) is int and 0<=r<9 and type(n) is int and n>=0, 'increment domain')
        m[r][9]+=n
    return m

# Parse only the explicit Lean Tree expression grammar, with no evaluation.
def parse_tree(s,name):
    start=re.search(r'\bdef '+re.escape(name)+r'\s*:\s*Tree\s*:=',s).end()
    i=start
    literal_token=re.compile(r'[()]|\.[a-zA-Z]+|[0-9]+')
    def token():
        nonlocal i
        while i<len(s) and s[i].isspace(): i+=1
        m=literal_token.match(s,i)
        check(m is not None, 'unexpected literal syntax at '+str(i))
        i+=len(m[0]); return m[0]
    def expr():
        t=token()
        if t=='(':
            v=expr();check(token()==')','unbalanced tree parentheses');return v
        if t=='.node':return ['node',expr(),expr()]
        if t=='.leaf':return ['leaf',expr()]
        if t=='.halt':return ['halt']
        if t in ['.inc','.decnz','.brk','.cont']:
            n=token();check(n.isdigit(),'instruction natural parameter');return [t[1:],int(n)]
        raise AssertionError('unhandled tree token '+t)
    return expr()

def leaves(t,p=''):
    if t[0]=='leaf':return [[p,t[1]]]
    check(t[0]=='node','invalid tree')
    return leaves(t[1],p+'0')+leaves(t[2],p+'1')

def increment(p):
    if not p:return ''
    return format((int(p,2)+1)%(1<<len(p)), '0'+str(len(p))+'b')
def strip(p,bit,n):
    while p and n:
        n-=int(p[-1]==bit);p=p[:-1]
    return p
def nextpath(p,op):
    if op[0]=='inc':return increment(p)
    if op[0]=='brk':return increment(strip(p,'0',op[1]))
    if op[0]=='cont':return strip(p,'1',op[1])
    raise AssertionError('unexpected non-test instruction')

def graph_from_tree(t):
    ls=leaves(t); bypath={p:i for i,(p,_) in enumerate(ls)}
    def decode(p):
        u=t;d=0
        while u[0]=='node':
            b=p[d] if d<len(p) else '0';u=u[1+int(b)];d+=1
        canonical=(p+'0'*d)[:d]
        return bypath[canonical],canonical,u[1]
    def segment(p):
        increments=collections.Counter();visited=set();route=[]
        while True:
            q,c,op=decode(p)
            if op[0] in ('decnz','halt'):
                return q,[[r,n] for r,n in sorted(increments.items())],route
            check(q not in visited,'infinite register-independent segment')
            visited.add(q);route.append(q)
            if op[0]=='inc':increments[op[1]]+=1
            p=nextpath(c,op)
    graph={};routes={}
    for i,(p,op) in enumerate(ls):
        if op[0]=='halt':graph[str(i)]={'op':op,'successors':[]}
        elif op[0]=='decnz':
            successors=[]
            for b,ptr in enumerate([increment(p),increment(strip(p,'0',1))]):
                q,incs,route=segment(ptr)
                successors.append([q,incs]);routes[f'{i}:{b}']=route
            graph[str(i)]={'op':op,'successors':successors}
    entry,incs,route=segment('')
    return graph,ls,routes,{'target':entry,'increments':incs,'route':route}

manifest=readj(PACK/'MANIFEST.json')
for n,v in manifest.items():
    p=PACK/n
    check(p.is_relative_to(PACK) and '..' not in p.parts,'unsafe path')
    check(p.stat().st_size==v['bytes'] and digest(p)==v['sha256'],'manifest '+n)
pins=readj(PACK/'graph_origin/SOURCE_PINS.json')
for p in pins['sources']:
    check(blob(PACK/'graph_origin/upstream'/p['name'])==p['git_blob_sha'],'source Git blob '+p['name'])
currentpins=readj(ROOT/'CURRENT_SOURCE_PINS.json')
for p in currentpins:
    check(blob(ROOT/'current_sources'/Path(p['path']).name)==p['git_blob_sha'],'current Git blob '+p['path'])
archive=ROOT.parent/'downloads/affine.zip'
archivepin=readj(ROOT/'INTAKE_PENDING.json')
check(blob(archive)==archivepin['git_blob_sha'],'archive Git blob')
text=(PACK/'graph_origin/upstream/KSource215Data.lean').read_text()
source_trees={k:parse_tree(text,n) for k,n in [('source','t215'),('reference','tD')]}
check(source_trees==readj(PACK/'graph_origin/trees.json'),'both literal trees')
for t in source_trees.values():
    check(all(0<=op[1]<9 for _,op in leaves(t) if op[0] in ('inc','decnz')), 'all accessed register indices below nine')
rebuilt={k:graph_from_tree(t) for k,t in source_trees.items()}
G=rebuilt['source'][0]
check(G==rebuilt['reference'][0],'independently rebuilt source/target graphs')
check(G==readj(PACK/'graph_origin/ordinal_graph.json'),'canonical stored graph')
check(G==readj(PACK/'structural/input_graph.json'),'affine input graph binding')
check({k:v[1] for k,v in rebuilt.items()}==readj(PACK/'graph_origin/leaves.json'),'both leaf/path lists')
for k,v in rebuilt.items():
    check(v[3]=={'target':0,'increments':[],'route':[]},'exact initial binding '+k)
    check([int(n) for n,x in v[0].items() if x['op']==['halt']]==[4736],'sole canonical halt')
# Check the balanced canonical relation table itself, including every branch
# left-size, canonical pointer, zero offset, and successor lookup index.
cert_text=(PACK/'graph_origin/CanonicalCert215.lean').read_text()
cert_start=re.search(r'def canonicalCert\s*:\s*OTree\s*:=',cert_text).end()
cert_tokens=re.compile(r'\.branch|\.leaf|[0-9]+|Int|[(),:]')
ci=cert_start
def ctok():
    global ci
    while ci<len(cert_text) and cert_text[ci].isspace():ci+=1
    m=cert_tokens.match(cert_text,ci)
    check(m is not None,'canonical certificate syntax')
    ci=m.end();return m[0]
def ceq(w):check(ctok()==w,'canonical certificate punctuation '+w)
def ctree():
    t=ctok()
    if t=='(':
        out=ctree();ceq(')');return out
    if t=='.branch':
        n=ctok();check(n.isdigit(),'canonical branch index')
        left=ctree();right=ctree()
        check(int(n)==len(left),'canonical branch left count')
        return left+right
    check(t=='.leaf','canonical tree constructor')
    ceq('(');a=int(ctok());ceq(',');b=int(ctok());ceq(',');ceq('(')
    z=int(ctok());ceq(':');ceq('Int');ceq(')');ceq(',')
    j=int(ctok());ceq(',');k=int(ctok());ceq(')')
    return [(a,b,z,j,k)]
cert=ctree()
ordinals={key:{path:i for i,(path,op) in enumerate(v[1])} for key,v in rebuilt.items()}
cert_ords=[]
for a,b,z,j,k in cert:
    check(a>0 and b>0 and z==0,'canonical pointer and zero-offset domain')
    pa=bin(a)[3:];pb=bin(b)[3:]
    check(pa in ordinals['source'] and pb in ordinals['reference'],'canonical exact leaf pointers')
    va=ordinals['source'][pa];vb=ordinals['reference'][pb]
    check(va==vb and str(va) in G,'canonical paired checkpoint binding')
    cert_ords.append(va)
check(len(cert)==len(G) and set(cert_ords)==set(map(int,G)),'canonical relation coverage and uniqueness')
check(cert_ords[0]==0,'canonical relation entry')
for row,v in zip(cert,cert_ords):
    node=G[str(v)]
    if node['op']==['halt']:continue
    for target_index,edge in zip(row[3:],node['successors']):
        check(0<=target_index<len(cert) and cert_ords[target_index]==edge[0],'canonical successor lookup binding')

phase5=ROOT/'current_sources/KSource215Data.phase5.lean'
phase5_pin=readj(ROOT/'CURRENT_PHASE5_SOURCE_PIN.json')
check(phase5.stat().st_size==phase5_pin['bytes'],'phase-five source byte count')
check(digest(phase5)==phase5_pin['sha256'],'phase-five source SHA-256 pin')
check(blob(phase5)==phase5_pin['git_blob_sha'],'phase-five source Git blob pin')
latest=phase5.read_text()
phase5_equal=all(parse_tree(latest,n)==source_trees[k] for k,n in [('source','t215'),('reference','tD')])
check(phase5_equal,'phase-five literal binding')

# Infer every eligible drain from the rebuilt graph before reading certificates.
D={}
for v,node in G.items():
    if node['op'][0]!='decnz':continue
    r=node['op'][1];pos,zero=node['successors']
    if pos[0]!=int(v) or any(i==r and c for i,c in pos[1]):continue
    m=ident();m[r]=[0]*10
    for i,c in pos[1]:m[i][r]+=c
    for i,c in zero[1]:m[i][9]+=c
    D[v]={'register':r,'increments':pos[1],'exit_increments':zero[1], 'target':zero[0],'matrix':m}
check(D==readj(PACK/'structural/drain_certificates.json'),'all drain bindings/matrices')
A=readj(PACK/'structural/affine_graph.json')
check(set(A)==set(G)-set(D),'affine retained domain')
drain_refs=[]
for v,node in A.items():
    check(node['op']==G[v]['op'],'affine opcode '+v)
    check(len(node['successors'])==len(G[v]['successors']),'affine edge count '+v)
    for i,edge in enumerate(node['successors']):
        q,incs=G[v]['successors'][i];m=incmat(incs)
        for d in edge['drain_path']:
            check(q==d and str(d) in D,'drain path binding '+v)
            c=D[str(d)];m=mul(c['matrix'],m);q=c['target'];drain_refs.append(d)
        check(str(q) in A and q==edge['target'],'drain path endpoint '+v)
        check(matrix_ok(edge['matrix']) and m==edge['matrix'],'drain product '+v)
C=readj(PACK/'structural/compact_affine_graph.json')
check(C['registers']==9 and C['nonzero_update']=='decrement_before_affine','compact semantics')
check(C['entry']=={'target':0,'matrix':ident(),'drain_path':[]},'affine initial identity')
check(set(C['nodes'])==set(A),'compact domain')
for v,node in C['nodes'].items():
    check(node['op']==A[v]['op'],'compact opcode')
    check(len(node['successors'])==len(A[v]['successors']),'compact edge arity')
    for pair,edge in zip(node['successors'],A[v]['successors']):
        check(pair[0]==edge['target'] and C['matrices'][pair[1]]==edge['matrix'],'compact reconstruction')
check(all(matrix_ok(m) for m in C['matrices']),'matrix well-formedness')

# Classify using the whole homogeneous transformation including decrement.
tri=ident();tri[1]=[0]*10;tri[6]=[0]*10;tri[6][1]=tri[6][6]=1;tri[6][9]=-1
tri[7][1]=tri[7][6]=1
clear=ident();clear[5]=[0]*10;clear[6][9]=-1
kinds={}
for v,node in A.items():
    if node['op']!=['decnz',6] or node['successors'][0]['target']!=int(v):continue
    m=[row[:] for row in node['successors'][0]['matrix']]
    for row in m:row[9]-=row[6]
    if m==tri:kinds[v]='triangular'
    elif m==clear:kinds[v]='clear'
K=readj(ROOT/'GUARDED_CORE.json')
compact_guarded=readj(ROOT/'GUARDED_CORE_COMPACT.json')
compact_guarded_bytes=(ROOT/'GUARDED_CORE_COMPACT.json').stat().st_size
shared=compact_guarded.pop('matrices')
check(all(matrix_ok(m) for m in shared),'guarded compact matrix well-formedness')
for node in compact_guarded['nodes'].values():
    for edge in node['successors']:
        j=edge['initial_affine'];check(type(j) is int and 0<=j<len(shared),'guarded compact matrix index')
        edge['initial_affine']=shared[j]
for loop in compact_guarded['loop_definitions'].values():
    j=loop['zero_exit']['matrix'];check(type(j) is int and 0<=j<len(shared),'guarded compact exit matrix index')
    loop['zero_exit']['matrix']=shared[j]
compact_guarded.pop('derived_exit_ranks',None)
check(compact_guarded=={k:v for k,v in K.items() if k!='derived_exit_ranks'},'compact guarded semantic round-trip excluding unused ranks')
check(K['loop_kinds']==kinds,'whole-register loop classification')
check(K['source_sha256']=={n:digest(PACK/n) for n in ['structural/input_graph.json','structural/affine_graph.json']},'guarded source digest bindings')
check(K['loop_definitions']=={v:{'kind':kind,'zero_exit':A[v]['successors'][1]} for v,kind in kinds.items()},'self-contained loop exit bindings')
check(set(K['nodes'])==set(A)-set(kinds),'guarded retained domain')
check(K['entry']==0 and '0' in K['nodes'],'guarded initial node')
check(K['halt']==[4736] and K['nodes']['4736']=={'op':['halt'],'successors':[]},'guarded sole halt')
paths=[];suffixes={}
for v,node in K['nodes'].items():
    check(node['op']==A[v]['op'],'guarded opcode')
    check(len(node['successors'])==len(A[v]['successors']),'guarded edge arity')
    for branch,edge in enumerate(node['successors']):
        src=A[v]['successors'][branch]
        check(edge['initial_affine']==src['matrix'],'guarded leading matrix')
        q=src['target'];path=edge['total_loop_path']
        for i,u in enumerate(path):
            check(u==q and str(u) in kinds,'guarded finite path binding')
            suffixes.setdefault(str(u), {'path':path[i:],'target':edge['target'],'source_edge':[int(v),branch],'offset':i})
            q=A[str(u)]['successors'][1]['target']
        check(q==edge['target'] and str(q) in K['nodes'],'guarded retained endpoint')
        paths.append(path)
check(set(suffixes)==set(kinds),'all removed vertices covered by existing suffixes')
check(set(map(str,drain_refs))==set(D),'all first-level drains covered by existing suffixes')
for v,w in suffixes.items():
    q=int(v)
    for u in w['path']:
        check(q==u,'arbitrary-entry suffix');q=A[str(q)]['successors'][1]['target']
    check(q==w['target'] and str(q) in K['nodes'],'arbitrary-entry suffix endpoint')

# Distinct local-summary interpreter, versus original graph and affine dynamics.
def step(g,v,r,affine):
    node=g[str(v)];check(node['op'][0]=='decnz','attempted halt transition')
    x=list(r);reg=node['op'][1];branch=0 if x[reg]>0 else 1
    if branch==0:x[reg]-=1
    e=node['successors'][branch]
    if affine:return e['target'],apply(e['matrix'],x)
    for i,c in e[1]:x[i]+=c
    return e[0],x

def closed(v,r):
    x=list(r);a=x[1];n=x[6]
    if n>0:
        x[6]=0
        if kinds[str(v)]=='triangular':x[1]=0;x[7]+=(a+n)*(a+n+1)//2
        else:x[5]=0
    e=A[str(v)]['successors'][1]
    return e['target'],apply(e['matrix'],x),1+(a+n if n>0 and kinds[str(v)]=='triangular' else n)

cases=0;primitive_steps=0;affine_steps=0
rng=random.Random(381661)
for v in kinds:
    for a in [0,1,2,5,8]:
      for n in [0,1,2,5,8]:
       for z in [0,1,9]:
        r=[rng.randrange(1,12) for _ in range(9)];r[1]=a;r[6]=n;r[7]=z
        target,expected,count=closed(v,r)
        u=int(v);x=r[:];steps=0
        while True:
            u,x=step(A,u,x,True);steps+=1
            if u!=int(v):break
            check(steps<10000,'affine local termination regression')
        check((u,x,steps)==(target,expected,count),'local affine summary '+v)
        affine_steps+=steps
        u=int(v);x=r[:];steps=0
        while True:
            u,x=step(G,u,x,False);steps+=1
            if str(u) in A and u!=int(v):break
            check(steps<100000,'original local termination regression')
        check((u,x)==(target,expected),'original graph local summary '+v)
        cases+=1;primitive_steps+=steps

# Mutational guards: demonstrate the failure of tempting unguarded summaries.
def mutation_example(v,r,mutator):
    target,right,_=closed(v,r)
    bad=list(r);mutator(bad)
    e=A[str(v)]['successors'][1];wrong=apply(e['matrix'],bad)
    check(right!=wrong,'mutation is unexpectedly invisible')
    return {'node':v,'input':r,'exit_target':target,'correct':right,'mutated':wrong}
bad_tri=mutation_example(36,[0,2,0,0,0,0,0,0,0],lambda r:(r.__setitem__(7,r[7]+(r[1]+r[6])*(r[1]+r[6]+1)//2),r.__setitem__(1,0),r.__setitem__(6,0)))
clear_zero=[]
for v,k in kinds.items():
    if k=='clear':
        r=[2,3,5,7,11,13,0,17,19];right=closed(v,r)[1];r[5]=0;wrong=apply(A[v]['successors'][1]['matrix'],r)
        clear_zero.append({'node':int(v),'wrong_clear_visible_after_exit':right!=wrong})
local_bindings={v:{'kind':k,'positive_matrix_after_decrement':A[v]['successors'][0]['matrix'],'zero_exit':A[v]['successors'][1]} for v,k in kinds.items()}
(HERE/'ENTRY_SUFFIX_CERTIFICATES.json').write_text(json.dumps(suffixes,indent=2)+'\n')
(HERE/'LOOP_BINDINGS.json').write_text(json.dumps({'affine_sha256':digest(PACK/'structural/affine_graph.json'),'loops':local_bindings},indent=2)+'\n')
report={'status':'PASS: independent finite and algebraic checks; no Lean/Rocq compilation',
 'manifest_payloads':len(manifest),'inherited_git_blobs':len(pins['sources']),'current_git_blobs':len(currentpins),
 'archive_git_blob':blob(archive),'archive_sha256':digest(archive),
 'guarded_core_sha256':digest(ROOT/'GUARDED_CORE.json'),
 'guarded_compact_sha256':digest(ROOT/'GUARDED_CORE_COMPACT.json'),'guarded_compact_bytes':compact_guarded_bytes,'guarded_compact_shared_matrices':len(shared),'guarded_compact_semantic_roundtrip':True,
 'canonical_relation_entries_checked':len(cert),'canonical_relation_all_offsets_zero':True,
 'both_source_literal_graphs_equal':True,'phase5_literal_trees_equal':phase5_equal,
 'phase5_source_git_blob':phase5_pin['git_blob_sha'],'phase5_source_sha256':phase5_pin['sha256'],
 'leaves_per_tree':{k:len(v[1]) for k,v in rebuilt.items()},'canonical_nodes':len(G),'canonical_edges':sum(len(n['successors']) for n in G.values()),
 'source_segment_lengths':{k:{'max':max(map(len,v[2].values())),'sum':sum(map(len,v[2].values()))} for k,v in rebuilt.items()},
 'source_entry_bindings':{k:v[3] for k,v in rebuilt.items()},'halt_ordinal':4736,
 'drains':len(D),'drain_path_references':len(drain_refs),'drains_covered_by_path_suffixes':len(set(drain_refs)),
 'affine_nodes':len(A),'affine_edges':sum(len(n['successors']) for n in A.values()),'affine_matrices':len(C['matrices']),
 'loop_counts':dict(collections.Counter(kinds.values())), 'guarded_nodes':len(K['nodes']),'guarded_edges':len(paths),
 'total_loop_references':sum(map(len,paths)),'max_loop_path':max(map(len,paths)),'removed_nodes_covered_by_suffixes':len(suffixes),
 'all_source_register_indices_below_nine':True,'higher_registers_framed_unchanged':True,
 'all_nine_registers_and_homogeneous_row_checked':True,'regression_cases':cases,'original_checkpoint_transitions':primitive_steps,'affine_transitions':affine_steps,
 'unguarded_triangle_counterexample':bad_tri,'clear_zero_mutation_observations':clear_zero,
 'rank_witnesses_used_for_acceptance':False,
 'claim_limits':['Finite literal/certificate validation and mathematical proof review only.','No received code executed.','No Lean/Rocq compiler was located; no kernel claim.','189 is a proof/checkpoint graph size, not a TM state count.']}
(HERE/'INDEPENDENT_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
