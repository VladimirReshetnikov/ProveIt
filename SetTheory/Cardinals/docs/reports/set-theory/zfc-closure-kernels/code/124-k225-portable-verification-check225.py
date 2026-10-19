#!/usr/bin/env python3
"""Independent complete source, whole blank frame, canonicalization and local-fold audit.

Standard library only. No incoming builder, runtime engine, search, or fold
verifier is imported. Exact input hashes bind the approved225 candidate.
The final225 universal runtime is a separate proof obligation.
"""
from pathlib import Path
from collections import deque
import argparse,hashlib,json,sys

def need(x,m):
    if not x: raise ValueError(m)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def digest(x):return hashlib.sha256((json.dumps(x,separators=(',',':'))+'\n').encode()).hexdigest()

def table(p):
    rows={};starts=[]
    for line in p.read_text().splitlines():
        if line.startswith('#! start '): starts.append(int(line[9:]))
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        need((q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R'),'invalid row')
        rows[q,b]=(w,1 if d=='R' else -1,z)
    states={q for q,b in rows};need(set(rows)=={(q,b)for q in states for b in (0,1)},'non-total table')
    terminal={z for w,d,z in rows.values()}-states
    need(len(starts)==1 and starts[0] in states and len(terminal)==1,'bad start/halt')
    return rows,starts[0],next(iter(terminal)),states

def rooted_serial(rows,start,halt,states):
    order=[start];mp={start:0}
    for q in order:
        for b in (0,1):
            z=rows[q,b][2]
            if z!=halt and z not in mp:mp[z]=len(mp);order.append(z)
    need(set(order)==states,'unreachable working state')
    return [[mp[q],b,w,d,mp[z] if z!=halt else 'H']for q in order for b in (0,1) for w,d,z in [rows[q,b]]]

def source(p):
    raw=json.loads(p.read_text());ops={'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'}
    rows=[]
    for r in raw:
        if len(r)==2:
            pc,cmd=r;parts=cmd.split();r=[pc,ops[parts[0]],int(parts[1]) if len(parts)>1 else None]
        pc,op,n=r
        need(pc and set(pc)<={'0','1'} and op in ('CI','CD','CB','CC','CH'),'bad source instruction')
        if op in ('CI','CD'):need(type(n)is int and 0<=n<9,'bad register')
        elif op in ('CB','CC'):need(type(n)is int and n>=1,'bad control count')
        else:need(n is None,'bad halt')
        rows.append(r)
    need(rows==sorted(rows),'unordered source');idx={r[0]:i for i,r in enumerate(rows)}
    need(len(rows)==len(idx),'duplicate leaves')
    prefixes={p[:k] for p in idx for k in range(len(p))}
    need(not prefixes.intersection(idx) and all(p+b in idx or p+b in prefixes for p in prefixes for b in '01'),'incomplete source tree')
    maxdepth=max(map(len,idx))
    def resolve(bits):
        node='';k=0
        while node not in idx:
            node+=bits[k] if k<len(bits) else '0';k+=1
            need(k<=maxdepth,'no leaf')
        need('1' not in bits[k:],'nonzero stray suffix')
        return idx[node]
    def inc(pc):
        n=int(pc,2)+1 if pc else 0
        return format(n%(2**len(pc)),'0'+str(len(pc))+'b') if pc else ''
    def trim(pc,b,n):
        for k in range(len(pc)-1,-1,-1):
            if pc[k]==b:
                n-=1
                if n==0:return pc[:k]
        return ''
    graph=[]
    for pc,op,n in rows:
        if op=='CH':succ=[]
        elif op=='CI':succ=[resolve(inc(pc))]
        elif op=='CD':succ=[resolve(inc(pc)),resolve(inc(trim(pc,'0',1)))]
        elif op=='CB':succ=[resolve(inc(trim(pc,'0',n)))]
        else:succ=[resolve(trim(pc,'1',n))]
        graph.append([op,n,succ])
    return rows,graph,resolve('')

def blank_frame(rows,start,halt,ticks,dispatcher):
    q=start;h=0;ones=set();used=set()
    for tick in range(ticks):
        need(q!=halt,'early halt');b=int(h in ones);used.add((q,b));w,d,q=rows[q,b]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    logical=[3,0,0,0,3,0,0,0,0];physical=[None]*9
    for i,j in enumerate([6,2,0,4,3,7,8,5,1]):physical[j]=logical[i]
    expected={-6,176};cursor=177
    for value in physical+[1]*167:
        cursor+=1;expected.update(range(cursor,cursor+value+1));cursor+=value+1
    need((q,h,ones)==(dispatcher,-5,expected),'wrong complete blank frame')
    return dict(status='EXACT_BLANK_FRAME_PASS',steps=ticks,dispatcher=q,head=h,one_cells=sorted(ones),all_other_cells=0,
                logical_registers=logical,physical_registers=physical,spares=[1]*167,extra_gap=117,rows_used=len(used))

def invariants(T,start,halt,radius=4):
    states={q for q,b in T};known={q:None for q in states};known[start]={};todo=deque([start]);updates=0
    def step(f,b,w,d):
        if 0 in f and f[0]!=b:return None
        g=dict(f);g[0]=w
        return {k-d:v for k,v in g.items()if -radius<=k-d<=radius}
    while todo:
        q=todo.popleft();f=known[q]
        for b in (0,1):
            w,d,z=T[q,b];g=step(f,b,w,d)
            if g is None or z==halt:continue
            old=known[z]
            new=g if old is None else {k:v for k,v in old.items()if g.get(k)==v}
            if old!=new:known[z]=new;todo.append(z);updates+=1
    need(all(v is not None for v in known.values()),'abstract-unreachable working state')
    need(known[start]=={},'initial invariant not universal')
    preservation=[]
    for (q,b),(w,d,z)in sorted(T.items()):
        g=step(known[q],b,w,d)
        if g is None:preservation.append([q,b,'guard-impossible']);continue
        if z!=halt:need(all(g.get(k)==v for k,v in known[z].items()),'invariant not inductive')
        preservation.append([q,b,'preserved'])
    return known,{'radius':radius,'updates':updates,'literal_row_obligations':preservation,
                  'state_facts':{str(q):f for q,f in sorted(known.items())},
                  'initial_state_unconstrained':True,
                  'method':'Forward finite known-bit intersection, followed by independent row-by-row inductiveness check including read guards. Holds from common start on every binary tape.'}


def local(old,new,start,halt):
    phi=lambda q:152 if q==229 else q
    expected={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in old.items()if q!=229}
    expected[152,0]=(0,-1,159);expected[152,1]=(1,-1,170)
    need(new==expected,'unexpected candidate edit')
    inv,certificate=invariants(old,start,halt)
    need(inv[152].get(-1)==1 and inv[229].get(-1)==0,'left tag guard unproved')
    need(start not in (152,229),'initial exceptional state')
    ordinary=0
    for (q,b),(w,d,z)in old.items():
        if q in (152,229):continue
        need(new[q,b]==(w,d,phi(z)),'ordinary row does not commute');ordinary+=1
    cases=[]
    for q,tag in ((152,1),(229,0)):
        for b in (0,1):
            cell={-1:tag,0:b};original=dict(cell);state=phi(q);head=0;trace=[]
            w,d,z=old[q,b];target=dict(cell);target[0]=w
            for j in range(3):
                need(head in cell,'helper reads unconstrained exterior')
                bit=cell[head];ww,dd,zz=new[state,bit]
                trace.append([state,head,bit,ww,dd,zz]);cell[head]=ww;head+=dd;state=zz
            need((state,head,cell)==(phi(z),d,target),'whole-tape block not exact')
            cases.append(dict(old_state=q,left_tag=tag,read=b,old_steps=1,new_steps=3,
                original_cells=original,old_row=[w,d,z],new_trace=trace,final_cells=cell,
                endpoint=[state,head],outside_cells_arbitrary_and_untouched=True))
    return dict(status='INDEPENDENT_ALL_TAPE_229_INTO_152_FOLD_PASS',ordinary_rows=ordinary,
        positive_blocks=cases,invariant=certificate,
        scope='From the common start0 on any binary initial tape and any initial head, rotated226 and final225 have matching positive blocks with exact whole tape. This fold proof does not establish preceding source rotations for arbitrary binary tapes.')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet-root',type=Path,default=Path(__file__).resolve().parents[1])
    ap.add_argument('--results-dir',type=Path)
    ap.add_argument('--output-dir',type=Path,required=True)
    args=ap.parse_args();ROOT=args.packet_root.resolve();C=(args.results_dir or ROOT/'results').resolve();P=args.output_dir.resolve()
    need(P!=ROOT and P not in (ROOT/'baseline226',ROOT/'results',ROOT/'verification'),'Output directory must not overwrite inputs')
    P.mkdir(parents=True,exist_ok=True)
    before=C/'rotated226.tm';after=C/'candidate225.klabels.tm';src=C/'sites225.json'
    oldlegacy,legacystart,legacyhalt,oldlegacystates=table(before)
    mapping=ROOT/'baseline226/source/legacy_state_map.json'
    mp={int(q):z for q,z in json.loads(mapping.read_text())['k230_to_old'].items()if z!=254};mp[254]=254
    need(len(set(mp.values()))==len(mp),'Noninjective inherited state map');mi={z:q for q,z in mp.items()}
    need(oldlegacystates|{legacyhalt}<=set(mi),'Unmapped old state')
    old={(mi[q],b):(w,d,mi[z])for(q,b),(w,d,z)in oldlegacy.items()};start=mi[legacystart];halt=mi[legacyhalt];oldstates={mi[q]for q in oldlegacystates}
    new,newstart,newhalt,states=table(after)
    need(sha(after)=='0847184fa05327daefa45c7012ce2c75fe58bf03d1dc930fe152e9fac55b4fbc','unexpected225 exact table')
    need(sha(src)=='86b28af08e646eb7da8b822f63a03173ef5182e5a2ebc0404008e1b2af41b55b','unexpected225 source')
    need((start,halt)==(newstart,newhalt)==(0,254)and len(oldstates)==226 and len(states)==225,'table census')
    base=ROOT/'baseline226/source/sites226.json'
    rs,g,e=source(src);br,bg,be=source(base)
    need([x[1:]for x in rs]==[x[1:]for x in br]and g==bg and e==be,'source graph changed')
    fold=local(old,new,start,halt)
    boot=blank_frame(new,start,halt,409835,84)
    controls=[]
    for label,mutator in (
        ('break152lefttag',lambda o,n:(o.__setitem__((67,1),(0,1,152)),n.__setitem__((67,1),(0,1,152)))),
        ('break229lefttag',lambda o,n:(o.__setitem__((184,0),(1,1,229)),n.__setitem__((184,0),(1,1,152)))),
        ('wrong_shared_helper',lambda o,n:(o.__setitem__((159,0),(0,1,154)),n.__setitem__((159,0),(0,1,154)))),
    ):
        badold,badnew=dict(old),dict(new);mutator(badold,badnew)
        try:local(badold,badnew,start,halt)
        except ValueError as error:controls.append(dict(control=label,rejected=True,reason=str(error)))
        else:raise ValueError('negative control unexpectedly accepted: '+label)
    # A literal state-name graph comparison also binds the legacy runtime table.
    legacy=C/'candidate225.tm';lt,ls,lh,lstates=table(legacy)
    need(rooted_serial(new,start,halt,states)==rooted_serial(lt,ls,lh,lstates),'legacy proof table differs modulo state names')
    canonical=C/'k225.tm';ct,cs,ch,cstates=table(canonical)
    renumpath=C/'renumbering225.json';renum=json.loads(renumpath.read_text());m={int(k):v for k,v in renum['k_to_canonical'].items()}
    need(set(m)==states|{halt}and set(m.values())==set(range(226))and len(set(m.values()))==len(m),'Canonical map not bijective')
    need(m[start]==cs==0 and m[halt]==ch==225 and cstates==set(range(225)),'Canonical state census')
    need(ct=={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in new.items()},'Literal canonical row mismatch')
    need(sha(canonical)=='f5d69a16a0324c69c8c6c407dbf18abcccf0e2d2a2283d5101ebc4591964140c','Unexpected canonical225 bytes')
    canonical_boot=blank_frame(ct,cs,ch,409835,m[84])
    result=dict(status='INDEPENDENT_225_SOURCE_LOCAL_FOLD_AND_STARTUP_PASS',
        checker_sha256=sha(Path(__file__)),
        table_sha256=sha(after),legacy_table_sha256=sha(legacy),rotated226_legacy_sha256=sha(before),source_sha256=sha(src),
        inherited_map_sha256=sha(mapping),canonical_sha256=sha(canonical),canonical_mapping_sha256=sha(renumpath),canonical_startup=canonical_boot,
        working_states=225,rows=450,start=start,halt=halt,source_leaves=len(rs),source_edges=sum(len(x[2])for x in g),
        source_graph_sha256=digest(g),initial_source_leaf=rs[e][0],maximum_source_depth=max(len(x[0])for x in rs),
        maximum_source_zero_run=max(len(z)for x in rs for z in x[0].split('1')),source_all_registers_equivalent=True,
        source_no_stray_successors=True,source_comparison_sha256=sha(base),
        legacy_runtime_table_isomorphic=True,local_fold=fold,blank_startup=boot,negative_controls=controls,
        scope='Independent literal/source/whole-blank audit and all-tape local fold. Full final225 universal binary runtime and upstream K230 calibration are separate obligations.')
    (P/'audit225.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in ('local_fold','blank_startup','canonical_startup')},indent=2))
    print('Ordinary rows',fold['ordinary_rows'],'four3-stepblocks','startup',boot['steps'])
if __name__=='__main__':main()
