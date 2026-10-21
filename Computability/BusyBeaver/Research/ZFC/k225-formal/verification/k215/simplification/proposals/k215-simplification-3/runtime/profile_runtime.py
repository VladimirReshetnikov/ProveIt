#!/usr/bin/env python3
"""Independent data-only replay/profile of the pinned K215 runtime.

This is NOT a Lean/Rocq proof or a kernel-performance measurement.
No imported repository executable is run. Uses only the standard library.
"""
from __future__ import annotations
import ast, collections, hashlib, json, re, sys
from pathlib import Path
if not __debug__:
    raise SystemExit('Assertions required: do not use -O or -OO.')
ROOT = Path(__file__).resolve().parent

def read(path):
    return (ROOT / path).read_text()

def verify_inputs():
    for name, digest in json.loads(read('input_hashes.json')).items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name

def literal(text):
    return ast.literal_eval(text.replace('true', 'True').replace('false', 'False').replace('none', 'None').replace('some ', ''))

def table_def(text, name, following):
    return literal(text.split('def '+name+' :', 1)[1].split(':=', 1)[1].split(following, 1)[0].strip())

class TrieParser:
    def __init__(self, text):
        self.tokens = re.findall(r'\.node|\.leaf|some|none|true|false|\d+|[(),]', text)
        assert re.sub(r'\s+', '', text) == ''.join(self.tokens)
        self.i = 0
    def pop(self, want=None):
        t = self.tokens[self.i]; self.i += 1
        if want is not None: assert t == want, (t, want)
        return t
    def row(self):
        self.pop('('); op = self.pop()
        if op == 'none': value = None
        else:
            assert op == 'some'; self.pop('(')
            b = self.pop(); self.pop(','); d = self.pop(); self.pop(','); q = int(self.pop())
            assert b in ('true','false') and d in ('true','false')
            self.pop(')'); value = (b == 'true', d == 'true', q)
        self.pop(')'); return value
    def tree(self):
        self.pop('('); op = self.pop()
        if op == '.node': out = (op, self.tree(), self.tree())
        else: assert op == '.leaf'; out = (op, self.row(), self.row())
        self.pop(')'); return out

def trie_lookup(tree, q, b):
    if q >= 256: return None
    while tree[0] == '.node':
        tree = tree[1 + q % 2]; q //= 2
    return tree[1 + bool(b)]

def load_tables():
    dense_file = (ROOT / 'inputs/k215.tm').read_bytes()
    assert hashlib.sha256(dense_file).hexdigest() == 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
    dense = {}
    for line in dense_file.decode().splitlines():
        if not line.strip() or line.startswith('#'): continue
        q,b,w,d,n = line.split(); key=(int(q),bool(int(b)))
        assert key not in dense and d in ('L','R')
        dense[key] = (bool(int(w)),d=='R',int(n))
    ds=read('latest/KDense215.lean')
    rows=table_def(ds,'rows215','\ndef act')
    labels=table_def(ds,'denseLabels','\ndef expand')
    assert len(rows)==len(labels)==215 and len(set(labels))==215
    assert dense == {(q,b): rows[q][int(b)] for q in range(215) for b in (False,True)}
    sparse=table_def(read('latest/KTable215.lean'),'table215','\ndef tm215')
    assert len(sparse)==226
    for (q,b),(w,d,n) in dense.items():
        assert sparse[labels[q]][int(b)] == (w,d,labels[n] if n<215 else 230)
    assert {(q,b) for q,row in enumerate(sparse) for b in (False,True) if row[int(b)] is not None} == {(q,b) for q in labels for b in (False,True)}
    text=read('latest/KFast215.lean').split('def tt215 : TT :=',1)[1].split('\ntheorem',1)[0].strip()
    parser=TrieParser(text); trie=parser.tree(); assert parser.i==len(parser.tokens)
    def depths(t,d=0):
        return [d] if t[0]=='.leaf' else depths(t[1],d+1)+depths(t[2],d+1)
    assert depths(trie)==[8]*256, 'Operation counts assume the exact eight-level trie'
    for q in range(257):
        for b in (False,True): assert trie_lookup(trie,q,b)==(sparse[q][int(b)] if q<len(sparse) else None)
    return dense,labels,sparse,trie

def checkpoint_data():
    out={}; t=0
    for i in range(13):
        text=read(f'inputs/KBoot215Chunk{i:03d}.lean')
        cp=literal(text.split(f'def cp{i+1} : LConf :=',1)[1].split('\ntheorem',1)[0].strip())
        depth=int(re.search(r'lblock \(fastOf tt215\) (\d+)',text).group(1))
        t+=2**depth; out[t]=cp
    assert t==95714
    return out

def bootstrap(dense,labels,sparse,trie):
    """Compare sparse-list Core, raw list zipper, and bounded integer bitset each step.

    Whole-tape equality is checked as equality of complete finite supports.
    All three representations define zero outside those supports. The bitset
    is range-checked before every access; no wrapped or truncated access exists.
    """
    lo,hi=-1024,1024
    q=0; h=0; ones=[]; zq=0; zh=0; left=[]; right=[]; bits=0
    cps=checkpoint_data(); cp_results=[]; heads=[0]; max_ones=0
    runs=[]; active=None; active_len=0; nonloops=0
    state_visits=collections.Counter(); visited_cells=set()
    for t in range(95714):
        assert lo<=h<=hi and lo<=zh<=hi
        sparse_bit=h in ones; zbit=right[0] if right else False; bit=(bits>>(h-lo))&1
        assert sparse_bit==zbit==bool(bit) and labels[q]==zq and h==zh
        w,d,n=dense[q,sparse_bit]
        zw,zd,zn=trie_lookup(trie,zq,zbit)
        assert (w,d,labels[n] if n<215 else 230)==(zw,zd,zn)
        state_visits[zq]+=1; visited_cells.add(h)
        key=(zq,zbit,zw,zd)
        if zn==zq:
            if key==active: active_len+=1
            else:
                if active is not None:runs.append((active,active_len))
                active=key;active_len=1
        else:
            nonloops+=1
            if active is not None:runs.append((active,active_len));active=None;active_len=0
        if w:
            if h not in ones:ones.insert(0,h)
            bits |= 1<<(h-lo)
        else:
            ones=[x for x in ones if x!=h]
            bits &= ~(1<<(h-lo))
        if zd:left=[zw]+left;right=right[1:];zh+=1
        else:left,right=left[1:],[(left[0] if left else False),zw]+right[1:];zh-=1
        q=n;h+=1 if d else -1;zq=zn;heads.append(h)
        assert q<215, 'Bootstrap unexpectedly halts'
        assert lo<=h<=hi and 0<=bits<2**(hi-lo+1)
        full_zip={zh-i-1 for i,b in enumerate(left) if b}|{zh+i for i,b in enumerate(right) if b}
        full_list=set(ones)
        assert len(full_list)==len(ones) and full_zip==full_list
        assert all(lo<=x<=hi for x in full_list)
        assert bits==sum(1<<(x-lo) for x in full_list)
        assert labels[q]==zq and h==zh
        max_ones=max(max_ones,len(ones))
        if t+1 in cps:
            cq,cl,cr=cps[t+1]
            assert (zq,left,right)==(cq,cl,cr)
            cp_results.append({'steps':t+1,'state':zq,'head':h,'left_length':len(left),'right_length':len(right)})
    if active is not None:runs.append((active,active_len))
    regs=[0,0,0,0,0,0,4,0,0]+[1]*40
    boot_right=[False]*65+[True]+sum(([False]+[True]*(v+1) for v in regs),[])
    assert zq==84 and left==[True]+[False]*9 and right==boot_right
    scan_steps=sum(n for _,n in runs)
    return {'transitions':95714,'whole_tape_comparisons':95714,'checkpoints_verified':cp_results,
            'fixed_bitset_bounds_inclusive':[lo,hi],'observed_head_bounds':[min(heads),max(heads)],
            'observed_write_bounds':[min(visited_cells),max(visited_cells)],'max_ones':max_ones,
            'final_state_sparse':zq,'final_state_dense':q,'final_head':h,'final_ones':sorted(ones),
            'selfloop_steps':scan_steps,'maximal_same_row_selfloop_scans':len(runs),
            'nonselfloop_steps':nonloops,'single_step_plus_scan_certificate_entries':nonloops+len(runs),
            'longest_scan':max(n for _,n in runs),
            'state_visits':dict(sorted(state_visits.items()))}

class TreeParser:
    def __init__(self,text):
        self.ts=re.findall(r'\.[A-Za-z]+|\d+|[()]',text)
        assert re.sub(r'\s+','',text)==''.join(self.ts)
        self.i=0
    def pop(self,w=None):
        t=self.ts[self.i];self.i+=1
        if w is not None:assert t==w
        return t
    def tree(self):
        self.pop('(');op=self.pop()
        if op=='.node':out=('node',self.tree(),self.tree())
        else:
            assert op=='.leaf'
            if self.ts[self.i]=='(':
                self.pop('(');k=self.pop()[1:];a=int(self.pop());self.pop(')')
            else:k=self.pop()[1:];assert k=='halt';a=None
            out=('leaf',k,a)
        self.pop(')');return out

def sites():
    text=read('inputs/KSource215Data.lean').split('def t215 : Tree :=',1)[1].split('/-- dagPerm',1)[0].strip()
    p=TreeParser(text);tree=p.tree();assert p.i==len(p.ts)
    out=[]
    def walk(t,path):
        if t[0]=='leaf':out.append((path,t[1:]))
        else:walk(t[1],path+(False,));walk(t[2],path+(True,))
    walk(tree,());assert len(out)==4751;return out

def inc(p):
    p=list(p)
    for i in range(len(p)-1,-1,-1):
        if not p[i]:p[i]=True;break
        p[i]=False
    return tuple(p)
def strip(p,b,k):
    i=len(p)
    while k and i:
        i-=1
        if p[i]==b:k-=1
    return p[:i]
def brk(p,k):return inc(strip(p,False,k))
def cont(p,k):return strip(p,True,k)
def bit(b):return ('bit',bool(b))
def run(b,a,c):return ('run',bool(b),a,c)
def box(x):return ('box',x)
PLAIN=('plain','none',None)
SK=[51,36,25,48,32,33,22,55,60]
PHYS=[6,2,0,4,3,7,8,5,1]

def oracle(q,br,x):
    if x==PLAIN:
        if q in SK:
            r=SK.index(q);return (1 if r==0 else 3,('mark',r),False)
    elif x[0]=='mark':
        r=x[1]
        if r<9:
            if q==64:return (40,('plain','inc',r),False)
            if q==0 and br is not None and br[0]==r:
                return (97,PLAIN,False) if br[1] else (40,('plain','dec',r),True)
    return None

def peel(q,onl,b,a,c,l,r):
    if c:
        segs=(bit(b),run(b,a,c-1))
        return ((q,onl,segs+l,r) if onl else (q,onl,l,segs+r),False)
    if a==0:return ((q,onl,l,r),False)
    return None

def sstep(M,br,s):
    q,onl,l,r=s
    if onl:
        if not l:return ((q,False,(),(bit(False),)+r),False)
        x=l[0];tail=l[1:]
        if x[0]=='bit':return ((q,False,tail,(x,)+r),False)
        if x[0]=='box':return None
        _,b,a,c=x;row=M(q,b)
        if row is not None and not row[1] and row[2]==q:return ((q,True,tail,(run(row[0],a,c),)+r),False)
        return peel(q,True,b,a,c,tail,r)
    if not r:return None
    x=r[0];tail=r[1:]
    if x[0]=='bit':
        row=M(q,x[1])
        if row is None:return None
        w,d,n=row
        return ((n,False,(bit(w),)+l,tail) if d else (n,True,l,(bit(w),)+tail),True)
    if x[0]=='run':
        _,b,a,c=x;row=M(q,b)
        if row is not None and row[1] and row[2]==q:return ((q,False,(run(row[0],a,c),)+l,tail),False)
        return peel(q,False,b,a,c,l,tail)
    assert x[0]=='box'
    if tail:return None
    o=oracle(q,br,x[1])
    if o is not None:
        n,y,extra=o;return ((n,True,((bit(True),)+l if extra else l),(box(y),)),False)
    row=M(q,False)
    if row is not None and row[:2]==(False,False):return ((row[2],True,l,r),True)
    return None

def norm(xs):
    acc=[]
    for x in reversed(xs):
        t=run(x[1],0,1) if x[0]=='bit' else x
        if t[0]=='run':
            if t[2:]==(0,0):continue
            if acc and acc[-1][0]=='run' and acc[-1][1]==t[1]:
                old=acc.pop();t=run(t[1],t[2]+old[2],t[3]+old[3])
        acc.append(t)
    return tuple(reversed(acc))
def normL(xs):
    ts=norm(xs)
    return ts[:-1] if ts and ts[-1][0]=='run' and not ts[-1][1] else ts
def matches(s,e):
    return s[:2]==e[:2] and norm(s[3])==norm(e[3]) and normL(s[2])==normL(e[2])
def start(p):return (84,False,(bit(True),),tuple(map(bit,p))+(run(False,1,64-len(p)),bit(True),box(PLAIN)))
def target(p,ovf,x):
    growth=int(x[0]=='plain' and x[1]=='dec')
    assert len(p)<=64+ovf+growth
    return (84,False,(bit(True),),tuple(map(bit,p))+(run(False,1,64+ovf+growth-len(p)),bit(True),box(x)))

def exec_trace(M,br,p,tgt):
    s=start(p);moved=False;out=[]
    for f in range(4000):
        if moved and (s[0]==230 if tgt is None else matches(s,tgt)):return s,out
        step=sstep(M,br,s)
        if step is None:return None,out
        s,m=step;out.append((s,m));moved=moved or m
    return None,out

def symbolic(sparse,trie):
    counts=collections.Counter();states=collections.Counter();lengths=[];expected_normalization_hits=0
    def Mlinear(q,b):
        counts['table_lookups']+=1;states[q]+=1
        counts['linear_list_cons_visits']+=min(q+1,len(sparse))
        # Deliberately implement a linear traversal, not Python list indexing.
        for i,row in enumerate(sparse):
            if i==q:return row[int(b)]
        return None
    def Mfast(q,b):
        counts['trie_lookups']+=1
        if q<256:counts['trie_internal_nodes']+=8
        return trie_lookup(trie,q,b)
    all_sites=sites();edge_counts=collections.Counter()
    for p,(k,a) in all_sites:
        assert len(p)<=48;edge_counts[k]+=1
        if k=='inc':assert a<9;tasks=[(None,target(inc(p),all(p),('plain','inc',PHYS[a])))]
        elif k=='decnz':
            assert a<9;r=PHYS[a]
            tasks=[((r,True),target(brk(p,1),all(strip(p,False,1)),PLAIN)),((r,False),target(inc(p),all(p),('plain','dec',r)))]
        elif k=='brk':tasks=[(None,target(brk(p,a),all(strip(p,False,a)),PLAIN))]
        elif k=='cont':tasks=[(None,target(cont(p,a),False,PLAIN))]
        else:assert k=='halt';tasks=[(None,None)]
        for branch,tgt in tasks:
            aout,atrace=exec_trace(Mlinear,branch,p,tgt)
            bout,btrace=exec_trace(Mfast,branch,p,tgt)
            assert aout is not None and aout==bout and atrace==btrace,(p,k,a,branch)
            counts['symbolic_runs']+=1;counts['symbolic_step_comparisons']+=len(atrace);lengths.append(len(atrace))
            if tgt is not None:
                # sMatches only computes normal forms once state AND side match.
                expected_normalization_hits+=sum(s[:2]==tgt[:2] for s,_ in atrace)
    assert counts['table_lookups']==counts['trie_lookups']
    return {'leaves':len(all_sites),'edge_counts':dict(edge_counts),'counts':dict(counts),
            'max_symbolic_steps':max(lengths),'min_symbolic_steps':min(lengths),
            'target_normal_form_candidate_checks':expected_normalization_hits,
            'linear_list_cons_visits_per_trie_internal_node':counts['linear_list_cons_visits']/counts['trie_internal_nodes'],
            'table_lookup_state_histogram':dict(sorted(states.items())),
            'interpretation':'Operation-shape counts only; NOT Lean reduction counts or a speedup measurement.'}

def main():
    verify_inputs();dense,labels,sparse,trie=load_tables()
    result={'status':'PASS','commit':'e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad',
            'trust_boundary':'Independent Python data/prototype checks only. No kernel compilation.',
            'table_checks':{'dense_rows':430,'sparse_operational_states':215,'trie_checked_q_values':257},
            'bootstrap':bootstrap(dense,labels,sparse,trie),'symbolic_sites':symbolic(sparse,trie)}
    (ROOT/'profile_result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('bootstrap','symbolic_sites')},indent=2))
    print('Bootstrap:',result['bootstrap']['observed_head_bounds'],result['bootstrap']['single_step_plus_scan_certificate_entries'],'single-step/scan entries')
    print('Sites:',result['symbolic_sites']['counts'])
if __name__=='__main__':main()
