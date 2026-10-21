#!/usr/bin/env python3
"""Data-only profile of literal Lean K215 forward-check computations.
Reads ../latest/KSource215Data.lean at e0b8f9cb; no network/Lean needed.
Python counters describe repeated mathematical queries, not kernel instruction
counts, elapsed-time estimates, or formal proof validation.
"""
from __future__ import annotations
import collections, hashlib, json, re, sys
from pathlib import Path
if not __debug__:
    raise SystemExit('Do not run with -O/-OO: assertions are required.')
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'latest/KSource215Data.lean'
raw=SOURCE.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='43093f181bfdd86408a7c88bbf8c0d99ada494b5e3780ae9d93cff05502dbe67'
s=raw.decode()
# Hash-cons exactly equal syntactic subtrees, preserving leaf constructor/argument.
nodes=[]; interning={}
def intern(node):
    if node not in interning: interning[node]=len(nodes); nodes.append(node)
    return interning[node]
class Tokens:
    def __init__(self,text):
        self.ts=re.findall(r'\.[A-Za-z]+|fwd\d+|Int|-?\d+|[(),:]',text)
        assert re.sub(r'\s+','',text)==''.join(self.ts), 'Unrecognized source token'
        self.pos=0
    def pop(self,expected=None):
        t=self.ts[self.pos];self.pos+=1
        if expected is not None: assert t==expected,(t,expected,self.pos)
        return t
    def tree(self):
        self.pop('(');op=self.pop()
        if op=='.node': out=intern(('node',self.tree(),self.tree()))
        else:
            assert op=='.leaf'
            if self.ts[self.pos]=='(':
                self.pop('(');kind=self.pop()[1:];arg=int(self.pop());self.pop(')')
            else: kind=self.pop()[1:];assert kind=='halt';arg=None
            out=intern(('leaf',kind,arg))
        self.pop(')');return out
    def otree(self,refs):
        self.pop('(');op=self.pop()
        if op=='.branch': out=('branch',int(self.pop()),self.otree(refs),self.otree(refs))
        elif op=='.leaf':
            self.pop('(');a=int(self.pop());self.pop(',');b=int(self.pop());self.pop(',')
            self.pop('(');z=int(self.pop());self.pop(':');self.pop('Int');self.pop(')');self.pop(',')
            u=int(self.pop());self.pop(',');v=int(self.pop());self.pop(')');out=('leaf',(a,b,z,u,v))
        else: assert op in refs;out=refs[op]
        self.pop(')');return out

def tree_def(name,next_marker):
    text=s.split('def '+name+' : Tree :=',1)[1].split(next_marker,1)[0].strip()
    tok=Tokens(text);out=tok.tree();assert tok.pos==len(tok.ts);return out
source=tree_def('t215','/-- dagPerm')
target=tree_def('tD','theorem t215_eq')
refs={}
for i in range(16):
    text=s.split(f'def fwd{i} : OTree :=',1)[1].split('\ndef ',1)[0].strip()
    tok=Tokens('('+text+')');refs[f'fwd{i}']=tok.otree(refs);assert tok.pos==len(tok.ts)
text=s.split('def fwdCert : OTree :=',1)[1].split('\nabbrev ',1)[0].strip()
tok=Tokens('('+text+')');cert=tok.otree(refs);assert tok.pos==len(tok.ts)
def flatten(t):
    if t[0]=='leaf':return [t[1]]
    left,right=flatten(t[2]),flatten(t[3]);assert t[1]==len(left)
    return left+right
entries=flatten(cert);assert len(entries)==2240 and {e[2] for e in entries}=={0}

stats=collections.Counter();decode_queries=collections.Counter();lookup_queries=collections.Counter()
site_queries=collections.Counter();site_depths={};segment_top=collections.Counter();segment_rec=collections.Counter();segment_results={}

def decode(n):
    stats['decode_calls']+=1;decode_queries[n]+=1
    assert n>=1 and n.bit_length()<=512
    bits=tuple(int(b) for b in bin(n)[3:])
    stats['decode_bit_iterations']+=len(bits)+1
    return bits

def lookup(j):
    lookup_queries[j]+=1;stats['certificate_lookup_calls']+=1
    t=cert;steps=0
    while t[0]=='branch':
        steps+=1
        if j<t[1]:t=t[2]
        else:j-=t[1];t=t[3]
    stats['certificate_lookup_internal_branches']+=steps
    return t[1]

def getc(j):
    a,b,z,_,_=lookup(j)
    return decode(a),decode(b),z

def inc(p):
    q=list(p)
    for i in range(len(q)-1,-1,-1):
        if not q[i]:q[i]=1;break
        q[i]=0
    return tuple(q)

def strip(p,bit,k):
    i=len(p)
    while k and i:
        i-=1
        if p[i]==bit:k-=1
    return p[:i]

def brk(p,k):return inc(strip(p,0,k))
def cont(p,k):return strip(p,1,k)

def site(root,p):
    site_queries[root,p]+=1
    t=root;d=0
    while nodes[t][0]=='node':
        b=p[d] if d<len(p) else 0
        t=nodes[t][1+b];d+=1
    stats['site_calls']+=1;stats['site_internal_nodes_visited']+=d
    site_depths[root,p]=d
    return nodes[t][1:],(p+(0,)*d)[:d]

def segment(root,p):
    stats['segment_top_calls']+=1;segment_top[root,p]+=1
    start=p;incs=[];walk=[];fuel=1000
    while fuel:
        segment_rec[root,p,fuel]+=1;walk.append(p)
        (kind,arg),q=site(root,p)
        if kind in ('decnz','halt'):
            out=(tuple(incs),p)
            old=segment_results.setdefault((root,start),out);assert old==out
            return out,tuple(walk)
        if kind=='inc':incs.append(arg);p=inc(q)
        elif kind=='brk':p=brk(q,arg)
        elif kind=='cont':p=cont(q,arg)
        else:raise AssertionError(kind)
        fuel-=1
    raise AssertionError('segment fuel exhausted')

walk_lengths=[]
def branch(a,b,j):
    stats['branch_checks']+=1
    (l1,p1),walk1=segment(source,a);(l2,p2),walk2=segment(target,b)
    walk_lengths.extend((len(walk1),len(walk2)))
    q1,q2,z=getc(j)
    assert z==0 and p1==q1 and p2==q2
    assert collections.Counter(l1)==collections.Counter(l2)

branch((),(),0)
for a,b,z,u,v in entries:
    p1,p2=decode(a),decode(b)
    (e1,q1),(e2,q2)=site(source,p1),site(target,p2)
    assert e1==e2 and z==0
    if e1[0]=='halt':stats['halt_entries']+=1;continue
    assert e1[0]=='decnz'
    branch(inc(q1),inc(q2),u)
    branch(brk(q1,1),brk(q2,1),v)

# Exact tree occurrence contexts. Prefix cannot simply be erased: KSim.start
# stores it on the tape and target successor calculations depend on it.
node_contexts=collections.defaultdict(list);leaves=[]
def occurrences(t,p):
    node_contexts[t].append(p)
    if nodes[t][0]=='leaf':leaves.append((t,p,nodes[t][1:]));return
    occurrences(nodes[t][1],p+(0,));occurrences(nodes[t][2],p+(1,))
occurrences(source,())
assert len(leaves)==4751
internal_ids=[t for t in node_contexts if nodes[t][0]=='node'];leaf_ids=[t for t in node_contexts if nodes[t][0]=='leaf']
assert len(internal_ids)==179
# Context-free command boundary effect skeletons, factoring only a common
# prefix of input and ALL outputs. This does NOT prove the machine execution
# treats that prefix parametrically.
effect_groups=collections.Counter(); edge_depths=collections.Counter();succ_groups=collections.Counter()
for t,p,(kind,arg) in leaves:
    if kind=='inc':outs=(inc(p),)
    elif kind=='decnz':outs=(inc(p),brk(p,1))
    elif kind=='brk':outs=(brk(p,arg),)
    elif kind=='cont':outs=(cont(p,arg),)
    else:outs=()
    common=len(p)
    for q in outs:
        k=0
        while k<min(len(p),len(q)) and p[k]==q[k]:k+=1
        common=min(common,k)
    if not outs:common=len(p)
    key=(kind,arg,p[common:],tuple(q[common:] for q in outs))
    effect_groups[key]+=1
    edge_depths[kind,arg,len(p)]+=1
    succ_groups[kind,arg,outs]+=1

def group_summary(counter):
    vals=list(counter.values())
    return {'calls':sum(vals),'unique':len(vals),'repeated_calls':sum(vals)-len(vals),'max_multiplicity':max(vals,default=0)}

def per_program(root):
    sq={p:n for (r,p),n in site_queries.items() if r==root}
    tq={p:n for (r,p),n in segment_top.items() if r==root}
    rq={(p,f):n for (r,p,f),n in segment_rec.items() if r==root}
    rec_paths=collections.Counter()
    for (p,f),n in rq.items():rec_paths[p]+=n
    header=[decode_raw(e[0 if root==source else 1]) for e in entries]
    return {'site_queries':group_summary(sq),'site_traversal_nodes':sum(n*site_depths[root,p] for p,n in sq.items()),'unique_site_traversal_nodes':sum(site_depths[root,p] for p in sq),'top_segment_queries':group_summary(tq),'recursive_segment_queries_exact_fuel':group_summary(rq),'recursive_segment_paths_ignoring_fuel':group_summary(rec_paths),'entry_header_paths_unique':len(set(header))}
def decode_raw(n):return tuple(int(b) for b in bin(n)[3:])

out={'status':'PASS_PYTHON_SOURCE_CHECKER_PROFILE_NOT_LEAN','commit':'e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad','source_sha256':hashlib.sha256(raw).hexdigest(),'forward_certificate_entries':len(entries),'counters':dict(stats),'decode_queries':group_summary(decode_queries),'certificate_lookup_queries':group_summary(lookup_queries),'site_queries':group_summary(site_queries),'top_segment_queries':group_summary(segment_top),'recursive_segment_queries_exact_fuel':group_summary(segment_rec),'max_segment_site_calls':max(walk_lengths),'source':per_program(source),'target':per_program(target),'source_tree_contexts':{'internal_unique_dag_nodes':len(internal_ids),'leaf_edge_kinds':len(leaf_ids),'all_unique_dag_nodes_including_leaves':len(node_contexts),'internal_node_occurrences':sum(len(node_contexts[t]) for t in internal_ids),'leaf_occurrences':len(leaves),'all_node_and_exact_prefix_contexts':sum(map(len,node_contexts.values())),'max_depth':max(len(p) for _,p,_ in leaves),'most_frequent_internal_node_context_count':max(len(node_contexts[t]) for t in internal_ids),'edge_and_depth_contexts':len(edge_depths),'exact_edge_and_successor_path_contexts':len(succ_groups),'common_prefix_factored_boundary_effect_patterns':len(effect_groups),'boundary_pattern_warning':'Only path-update boundary patterns; NOT a parametrized TM execution proof or a sound site-check quotient.'},'top_shared_internal_nodes':[{'intern_id':t,'contexts':len(node_contexts[t]),'min_prefix_length':min(map(len,node_contexts[t])),'max_prefix_length':max(map(len,node_contexts[t]))} for t in sorted(internal_ids,key=lambda t:-len(node_contexts[t]))[:20]],'boundary_effect_pattern_distribution':[{'kind':k[0],'arg':k[1],'input_suffix':''.join(map(str,k[2])),'output_suffixes':[''.join(map(str,q)) for q in k[3]],'count':v} for k,v in effect_groups.most_common()]}
(ROOT/'forward_profile.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='boundary_effect_pattern_distribution'},indent=2))
