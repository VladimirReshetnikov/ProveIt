#!/usr/bin/env python3
"""Rebuild the exact seven-rotation, context-folded235 candidate.

Python3.10+ standard library; run with assertions enabled. This script proves
all source guard graphs agree and compares the complete blank startup. The
unbounded binary runtime theorem and independent all-tape local-fold proof
are separate artifacts; a bounded discovery run is not used as their proof.

Usage:
 python3 -B build_zfc235.py --baseline-dir EXTRACTED_236_PACKAGE \
   --output-dir NEW_DIRECTORY
"""
from pathlib import Path
from functools import cache
from collections import Counter,defaultdict
import argparse,hashlib,json,sys

TABLE236='ff059535876bc9e1e1e63174ebfd1c10a91c1a818ba0c3f8c4ef2ac51a3cfcc3'
SOURCE236='1ebe9691507b2d3236951a31d6b9a7ef548a2cdf90525cd57051992f8ac2626f'
BASIS236='014133f39c409277c239fa327db17800b4e886a5c7a5a73034ed87e4978820aa'
SOURCE235='c17ab40e032e79dca03eaa955a78dbcd65bd030795ecc232dc504aff1551cb20'
TABLE235='d017abe46023a4154085a2fe2c04c8d66bbbec53b81d193d520ad697d171cbd4'
STAGES=((138,211,'right'),(116,134,'left'),(162,116,'left'),
        (199,227,'left'),(227,197,'right'),(197,115,'right'),
        (115,229,'right'))
START,DISPATCH,HALT,BOOT=95,96,254,409835

def require(p,m):
    if not p:raise ValueError(m)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def json_bytes(obj,compact=False):
    return (json.dumps(obj,separators=(',',':'))+'\n').encode() if compact else (json.dumps(obj,indent=2)+'\n').encode()
def read_table(raw):
    rows={};starts=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]));continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        require((q,b) not in rows and b in(0,1) and w in(0,1) and d in('L','R'),'Malformed row')
        rows[q,b]=(w,1 if d=='R' else -1,z)
    states={q for q,b in rows}
    require(starts==[START],'Unexpected inherited start')
    require(set(rows)=={(q,b) for q in states for b in(0,1)},'Table is partial')
    require({z for w,d,z in rows.values()}-states=={HALT},'Unexpected halt')
    return rows

def encode(t,start=START):
    return (f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for(q,b),(w,d,z) in sorted(t.items()))).encode()

def is_leaf(t):return isinstance(t[0],str)
def tree(rows):
    trie={};seen=set()
    for p,o,r in rows:
        require(p and not(set(p)-{'0','1'}) and p not in seen,'Malformed/duplicate source path');seen.add(p)
        require(o in('CI','CD','CB','CC','CH'),'Source opcode')
        require((o=='CH' and r is None) or (o!='CH' and type(r) is int and r>=0),'Source operand')
        require(o not in('CI','CD') or r<9,'Source register')
        at=trie
        for b in p:
            require('leaf' not in at,'Source is not prefix-free');at=at.setdefault(b,{})
        require(not at,'Repeated/overlapping source leaf');at['leaf']=(o,r)
    def visit(n):
        if 'leaf' in n:
            require(set(n)=={'leaf'},'Leaf with children');return n['leaf']
        require(set(n)=={'0','1'},'Non-full source tree');return visit(n['0']),visit(n['1'])
    return visit(trie)

def sites(t,p=''):
    if is_leaf(t):return [(p,*t)]
    return sites(t[0],p+'0')+sites(t[1],p+'1')

@cache
def boundary(t):
    if is_leaf(t):
        o,r=t
        return (1,0,False) if o=='CD' else (r,0,False) if o=='CB' else (0,r,False) if o=='CC' else (0,0,o=='CH')
    a,b=map(boundary,t)
    return max(max(a[0]-1,0),b[0]),max(a[1],max(b[1]-1,0)),a[2] or b[2]

def graph(rows):
    ordered=sorted(tuple(x) for x in rows);leaves={p:i for i,(p,o,r) in enumerate(ordered)}
    prefixes={p[:k] for p in leaves for k in range(len(p))};mx=max(map(len,leaves))
    require(not(set(leaves)&prefixes),'Source is not prefix-free')
    require(all(p+c in prefixes or p+c in leaves for p in prefixes for c in'01'),'Source is not full')
    def locate(p):
        word=p+'0'*mx
        for k in range(1,mx+1):
            if word[:k] in leaves:
                require('1' not in p[k:],'Noncanonical successor suffix');return leaves[word[:k]]
        raise ValueError('Unresolved source successor')
    def inc(p):return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b') if p else ''
    def cut(p,c,k):
        if k==0:return p
        pos=[i for i,b in enumerate(p) if b==c]
        return p[:pos[-k]] if len(pos)>=k else ''
    gg=[]
    for p,o,r in ordered:
        if o=='CI':gg.append(('INC',r,locate(inc(p))))
        elif o=='CD':gg.append(('DEC',r,locate(inc(p)),locate(inc(cut(p,'0',1)))))
        elif o=='CB':gg.append(('JUMP',locate(inc(cut(p,'0',r)))))
        elif o=='CC':gg.append(('JUMP',locate(cut(p,'1',r))))
        else:gg.append(('HALT',))
    return ordered,gg,locate('')

def metrics(t):
    live=set()
    def visit(n):
        if n in live:return
        live.add(n)
        if not is_leaf(n):visit(n[0]);visit(n[1])
    visit(t);ss=sites(t)
    return dict(dag_nodes=len(live),leaf_occurrences=len(ss),maximum_depth=max(len(p) for p,o,r in ss),
                maximum_zero_run=max(len(z) for p,o,r in ss for z in p.split('1')))

def decoder_mapping(root,t):
    m={};inverse=defaultdict(set)
    def visit(n,q):
        if is_leaf(n):return
        if n in m:require(m[n]==q,'Inconsistent source decoder mapping');return
        m[n]=q;inverse[q].add(n)
        for b in(0,1):
            w,d,z=t[q,b]
            if (w,d)==(b,1):visit(n[b],z)
    visit(root,DISPATCH);return m,inverse

def stage(root,t,q,q2,direction):
    mapping,inverse=decoder_mapping(root,t)
    require(len(inverse[q])==1 and len(inverse[q2])==1,'Ambiguous decoder states')
    n=next(iter(inverse[q]));child=n[1 if direction=='left' else 0]
    require(not is_leaf(child) and mapping[child]==q2,'Unexpected child state')
    require(all(t[p,b][:2]==(b,1) for p in(q,q2) for b in(0,1)),'A rotation row is not a pure decoder step')
    incoming=[(p,b) for(p,b),(w,d,z) in t.items() if z==q2]
    require(incoming==[(q,1 if direction=='left' else 0)],'Intermediate decoder state has another incoming row')
    if direction=='left':a,(b,c)=n;replacement=(a,b),c
    else:(a,b),c=n;replacement=a,(b,c)
    chunks=(a,b,c)
    require(all(boundary(v)==(0,0,False) for v in chunks),'A source chunk has escaping control or a halt')
    paths=[]
    def occurrences(v,p=''):
        if v==n:paths.append(p);return
        if not is_leaf(v):occurrences(v[0],p+'0');occurrences(v[1],p+'1')
    occurrences(root)
    @cache
    def replace(v):
        if v==n:return replacement
        return v if is_leaf(v) else (replace(v[0]),replace(v[1]))
    newroot=replace(root);new=dict(t)
    if direction=='left':
        qa=t[q,0][2];qb=t[q2,0][2];qc=t[q2,1][2]
        new[q,0]=(0,1,q2);new[q,1]=(1,1,qc);new[q2,0]=(0,1,qa);new[q2,1]=(1,1,qb)
    else:
        qa=t[q2,0][2];qb=t[q2,1][2];qc=t[q,1][2]
        new[q,0]=(0,1,qa);new[q,1]=(1,1,q2);new[q2,0]=(0,1,qb);new[q2,1]=(1,1,qc)
    cert=dict(direction=direction,outer_state=q,inner_state=q2,paths=paths,
              chunk_leaf_counts=[len(sites(v)) for v in chunks],chunk_boundaries=[boundary(v) for v in chunks],
              literal_edits=[dict(row=[p,b],before=t[p,b],after=new[p,b]) for p,b in sorted(new) if t[p,b]!=new[p,b]],
              metrics=metrics(newroot))
    return newroot,new,cert

def startup(old,new):
    qo=qn=START;ho=hn=0;so=set();sn=set();visited=Counter()
    changed={k for k in old if k not in new or old[k]!=new[k]}
    for tick in range(BOOT):
        require((qo,ho,so)==(qn,hn,sn),f'Startup differs before step{tick}')
        row=qo,int(ho in so);visited[row]+=1
        require(row not in changed,'A changed/deleted row was used during startup')
        wo,do,zo=old[row];wn,dn,zn=new[qn,int(hn in sn)]
        if wo:so.add(ho)
        else:so.discard(ho)
        if wn:sn.add(hn)
        else:sn.discard(hn)
        qo,ho=zo,ho+do;qn,hn=zn,hn+dn
    require((qo,ho,so)==(qn,hn,sn),'Different final startup configurations')
    require((qn,hn,len(sn))==(DISPATCH,-5,351),'Wrong startup frame')
    return dict(status='EXACT_STARTUP_PASS',steps=BOOT,matched_checkpoints=BOOT+1,
                changed_or_deleted_rows_visited=0,endpoint_state=qn,head=hn,one_cells=sorted(sn),
                visited_rows=[dict(row=list(k),visits=v) for k,v in sorted(visited.items())])

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline-dir',type=Path)
    ap.add_argument('--baseline-table',type=Path);ap.add_argument('--baseline-source',type=Path)
    ap.add_argument('--output-dir',type=Path,required=True);a=ap.parse_args()
    if a.baseline_dir is not None:
        require(a.baseline_table is None and a.baseline_source is None,'Use baseline-dir or explicit input paths, not both')
        a.baseline_table=a.baseline_dir/'machines/zfc236_old.tm'
        a.baseline_source=a.baseline_dir/'source/sites_logical.json'
    require(a.baseline_table is not None and a.baseline_source is not None,'Provide baseline-dir or both explicit input paths')
    raw=a.baseline_table.read_bytes();src=a.baseline_source.read_bytes()
    require(sha(raw)==TABLE236,'Wrong pinned236table');require(sha(src)==SOURCE236,'Wrong pinned236source')
    old=read_table(raw);require(len(old)==472,'236input state count')
    ss=json.loads(src);root=tree(ss);initial_metrics=metrics(root)
    ordered,reference,initial=graph(ss);table=dict(old);stages=[]
    for number,(q,q2,direction) in enumerate(STAGES,1):
        root,table,cert=stage(root,table,q,q2,direction);ss=sites(root);word,g,i=graph(ss)
        require([r[1:] for r in word]==[r[1:] for r in ordered],'Instruction order changed')
        require(g==reference and i==initial,'A source guard successor changed')
        stages.append(dict(number=number,**cert))
    require(sha(encode(table))==BASIS236,'Unexpected rotated236table bytes')
    source_bytes=json_bytes(sites(root),compact=True);require(sha(source_bytes)==SOURCE235,'Unexpected source bytes')
    final_metrics=metrics(root);require(final_metrics==dict(dag_nodes=224,leaf_occurrences=6455,maximum_depth=48,maximum_zero_run=6),'Unexpected final source metrics')
    folded={(q,b):(w,d,74 if z==193 else z) for(q,b),(w,d,z) in table.items() if q!=193}
    folded[74,0]=(0,-1,138);folded[74,1]=(1,-1,116)
    require(len(folded)==470 and sha(encode(folded))==TABLE235,'Unexpected235table bytes')
    states={q for q,b in folded};order=[START]+sorted(states-{START});mapping={q:i for i,q in enumerate(order)}|{HALT:235}
    canonical={(mapping[q],b):(w,d,mapping[z]) for(q,b),(w,d,z) in folded.items()}
    require(set(canonical)=={(q,b) for q in range(235) for b in(0,1)},'Canonical table is partial')
    boot=startup(old,folded)
    cert=dict(format='zfc235-closed-source-rotation-certificate-v1',status='PASS_ALL_SOURCE_GUARDS',
              baseline_source_sha256=SOURCE236,source_sha256=SOURCE235,baseline_table_sha256=TABLE236,
              rotated_basis_sha256=BASIS236,stages=stages,initial_metrics=initial_metrics,final_metrics=final_metrics,
              changed_leaf_paths=sum(a[0]!=b[0] for a,b in zip(ordered,word)),
              changed_basis_rows=sum(old[k]!=table[k] for k in old),
              basis_literal_edits=[dict(row=[q,b],before=old[q,b],after=table[q,b])
                                   for q,b in sorted(table) if table[q,b]!=old[q,b]],
              guarded_cases=sum(2 if r[0]=='DEC' else 1 for r in reference),
              source_scope='Every source configuration over arbitrary natural registers; binary runtime is a separate proof.')
    construction=dict(status='EXACT_CONSTRUCTION_AND_STARTUP_PASS',working_states=235,transition_rows=470,
                      inherited_start=START,inherited_dispatcher=DISPATCH,inherited_halt=HALT,
                      deleted_state=193,retained_state=74,inherited_sha256=TABLE235,
                      canonical_sha256=sha(encode(canonical,0)),source_sha256=SOURCE235,
                      rotated_basis_sha256=BASIS236,rotation_count=len(stages),startup_steps=BOOT,
                      changed_rows=[dict(row=[q,b],before=old[q,b],after=folded[q,b]) for q,b in sorted(folded) if folded[q,b]!=old[q,b]],
                      scope='Source graph and startup certificates; all-tape fold and unbounded runtime proofs are separate.')
    a.output_dir.mkdir(parents=True,exist_ok=True)
    files={'zfc_rotated236_old.tm':encode(table),'zfc235_old.tm':encode(folded),'zfc235.tm':encode(canonical,0),
           'sites_logical.json':source_bytes,'source_rotation_certificate.json':json_bytes(cert),
           'renumbering235.json':json_bytes(dict(old_to_new=mapping,new_to_old=order+[HALT],start_old=START,start_new=0,
                                               dispatcher_old=DISPATCH,dispatcher_new=mapping[DISPATCH],halt_old=HALT,halt_new=235)),
           'startup235.json':json_bytes(boot),'construction235.json':json_bytes(construction)}
    for name,data in files.items():(a.output_dir/name).write_bytes(data)
    print(json.dumps(construction,indent=2))

if __name__=='__main__':
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Run without -O/-OO')
    main()
