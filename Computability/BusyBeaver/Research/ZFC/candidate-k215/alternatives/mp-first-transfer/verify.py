#!/usr/bin/env python3
"""Reconstruct and check the exact T215 candidate; Python 3.10+, offline.
Default: literal construction, independent CFGs, exact full-tape bootstrap,
mathematics certificates, and stored runtime census.
--runtime: additionally derive every arbitrary-natural whole-tape case anew.
"""
from pathlib import Path
import argparse, gzip, hashlib, json, os, sys, tempfile, time, subprocess
R = Path(__file__).resolve().parent
sys.path[:0] = [str(R/'code'), str(R/'reference/transfer-parent/checks')]
import source_language as L
import source_utils as U
import independent_runtime as I
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_text())
def dump(p, x): Path(p).write_text(json.dumps(x, indent=2)+'\n')
def require(x, message):
    if not x: raise ValueError(message)

def frame(path, regs, spares, gap=0, head=0):
    """Independent literal whole-tape frame constructor, with zero exterior."""
    values = [regs[i] for i in (2,8,1,4,3,7,0,5,6)]
    support = {head-1, head+64+gap}
    support.update(head+i for i,b in enumerate(path) if b=='1')
    cursor = head+65+gap
    for v in values+list(spares):
        require(type(v) is int and v>=0, 'Frame value not natural')
        support.update(range(cursor+1, cursor+v+2))
        cursor += v+2
    return support

def local_graph(sites, graph, prefix):
    ids = [i for i,(p,op,a) in enumerate(sites) if p.startswith(prefix)]
    a,b = min(ids),max(ids)+1
    require(ids==list(range(a,b)), 'Noncontiguous body')
    out=[]
    for i in ids:
        effect,edges=graph[i]
        require(all(a<=v<b or v==b%len(sites) for v in edges), 'Body is not closed')
        out.append([effect,[v-a if a<=v<b else 'EXIT' for v in edges]])
    return out

def reconstruction():
    recipe=read(R/'machine/recipe.json');sr=recipe['source_recipe']
    parent=R/sr['parent'];require(H(parent)==sr['parent_sha256'],'Source parent hash')
    oldsites=read(parent);old=L.tree(oldsites);left,right=sr['swap_closed_subtrees']
    a,b=L.subtree(old,left),L.subtree(old,right)
    require(L.boundary(a)[:2]==(0,0) and L.boundary(b)[:2]==(0,0), 'Closed source bodies')
    new=L.replace(L.replace(old,left,b),right,a);sites=L.sites(new)
    require(sites==read(R/'machine/sites215.json'),'Source reconstruction')
    require(H(R/'machine/sites215.json')==sr['output_sha256'],'Source hash')
    G,checks=L.graph_arithmetic(sites);require(G==L.graph_intervals(sites),'Independent source CFGs')
    oldG,_=L.graph_arithmetic(oldsites)
    require(local_graph(oldsites,oldG,left)==local_graph(sites,G,right),'Moved body 1')
    require(local_graph(oldsites,oldG,right)==local_graph(sites,G,left),'Moved body 2')
    # All other leaves retain their exact instruction and target paths.
    lookup={p:i for i,(p,op,k) in enumerate(sites)}
    def remap(p):
        if p.startswith(left):return right+p[len(left):]
        if p.startswith(right):return left+p[len(right):]
        return p
    exterior=0
    for i,(p,op,k) in enumerate(oldsites):
        if p.startswith(left) or p.startswith(right):continue
        ni=lookup[p];require(sites[ni][1:]==[op,k],'Exterior effect')
        # The dispatch edges intentionally go to the replacement body at the
        # same selector address, rather than follow its old semantic identity.
        def target_path(v):
            oldpath=oldsites[v][0]
            for prefix in (left,right):
                if oldpath.startswith(prefix):
                    bodyids=[j for j,s in enumerate(oldsites) if s[0].startswith(prefix)]
                    if v==bodyids[0]:
                        return next(s[0] for s in sites if s[0].startswith(prefix))
            return oldpath
        require(G[ni][0]==oldG[i][0], 'Exterior CFG effect')
        require([sites[v][0] for v in G[ni][1]]==[target_path(v) for v in oldG[i][1]],'Exterior CFG targets')
        exterior+=1
    require(G[23][0]==['decrement',3] and G[24][0]==['decrement',3], 'Two selector decrements')
    require(sites[G[23][1][0]][0].startswith('111'), 'Tag zero enters MP')
    require(sites[G[24][1][0]][0].startswith('110101'), 'Tag one enters S')
    require(G[24][1][1]==25,'Tags at least two enter AX')
    parent=R/recipe['parent'];require(H(parent)==recipe['parent_sha256'],'Table parent hash')
    T=U.parse_table(parent)
    for edit in recipe['edits']:
        key=tuple(edit['key']);require(T[key]==tuple(edit['old']),'Old literal row')
        T[key]=tuple(edit['new'])
    require(U.encode(T)==(R/'machine/t215.native.tm').read_bytes(),'Literal row reconstruction')
    require(H(R/'machine/t215.native.tm')==recipe['output_sha256'],'Table hash')
    qs={q for q,b in T};require(len(qs)==215 and len(T)==430 and 254 not in qs,'Working-state count')
    require(all((q,b) in T for q in qs for b in (0,1)), 'Total binary table')
    require(all(w in (0,1) and d in (-1,1) and z in qs|{254} for w,d,z in T.values()),'Valid actions')
    m={q:i for i,q in enumerate(sorted(qs))};m[254]=215
    K=I.table(R/'machine/t215.tm');require(K=={(m[q],b):(w,d,m[z]) for (q,b),(w,d,z) in T.items()},'Dense bijection')
    cm=read(R/'machine/canonicalization.json')
    require(m=={int(q):v for q,v in cm['native_to_dense'].items()},'Canonicalization record')
    reach={0};queue=[0]
    for q in queue:
        for b in (0,1):
            v=T[q,b][2]
            if v!=254 and v not in reach:reach.add(v);queue.append(v)
    require(reach==qs,'Every state graph-reachable from start')
    info={'status':'PASS','source':L.metrics(new),'guarded_cases':sum(2 if op=='CD' else 1 for p,op,k in sites),'source_successor_checks':checks,'unchanged_exterior_leaves':exterior,'closed_body_transports':2,'changed_transition_rows':len(recipe['edits']),'working_states':len(qs),'transition_rows':len(T),'all_working_states_graph_reachable':True,'source_sha256':H(R/'machine/sites215.json'),'native_sha256':H(R/'machine/t215.native.tm'),'dense_sha256':H(R/'machine/t215.tm')}
    return sites,G,T,K,m,info

def startup(sites,G,T,K,m,W):
    wantregs=[1,11,2,0,0,0,0,0,0];spares=[1]*59
    require(sites[55][0]=='110100100101010','Bootstrap source address')
    expected=frame(sites[55][0],wantregs,spares,head=-2)
    require(expected=={x-2 for x in I.frame(sites[55][0],wantregs,spares,0)},'Independent frame constructors')
    q=h=qc=hc=qd=hd=0;ones=set();canon=set();left=bytearray(4096);right=bytearray(4096);maxabs=0
    for tick in range(68442):
        w,d,q=T[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
        w,d,qc=K[qc,int(hc in canon)]
        if w:canon.add(hc)
        else:canon.discard(hc)
        hc+=d
        require((qc,hc,canon)==(m[q],h,ones),'Canonical lockstep')
        cells,j=(right,hd) if hd>=0 else (left,-hd-1)
        require(j<len(cells),'Independent dense interpreter capacity')
        w,d,qd=T[qd,cells[j]];cells[j]=w;hd+=d;maxabs=max(maxabs,abs(hd))
    dense={i for i,b in enumerate(right) if b}|{-i-1 for i,b in enumerate(left) if b}
    require((q,h)==(qd,hd)==(84,-2) and ones==dense==expected,'Complete blank frame')
    pc=25;regs=[1,0,4,0,0,0,0,0,0];trace=[]
    for step in range(174):
        trace.append([pc,regs.copy()]);effect,targets=G[pc];kind=effect[0]
        if kind=='increment':regs[effect[1]]+=1;pc=targets[0]
        elif kind=='decrement':
            r=effect[1]
            if regs[r]:regs[r]-=1;pc=targets[1]
            else:pc=targets[0]
        else:require(kind=='identity','No halt in AX prefix');pc=targets[0]
    require(pc==55 and regs==wantregs,'Exact synthetic AX computation')
    parent=read(R/'reference/transfer-parent/evidence/ax_bootstrap_match.json')
    require(trace==parent['trace'],'Unchanged AX-prefix trace')
    dump(W/'bootstrap_source_trace.json',{'entry':25,'entry_registers':[1,0,4,0,0,0,0,0,0],'exit':55,'exit_registers':regs,'trace':trace})
    dump(W/'bootstrap_frame.json',{'state':q,'dense_state':qc,'head':h,'gap':0,'address':sites[55][0],'logical':wantregs,'spares':spares,'one_cells':sorted(ones)})
    return {'status':'EXACT_WHOLE_TAPE_MATCH','transitions':68442,'source_ordinal':55,'head':h,'logical':wantregs,'spare_count':59,'spare_value':1,'ones':len(ones),'largest_head_distance':maxabs,'source_prefix_steps':174,'independent_tape_representations':2,'dense_native_lockstep':True,'source_trace_sha256':H(W/'bootstrap_source_trace.json'),'frame_sha256':H(W/'bootstrap_frame.json')}

def stored_census(sites):
    cases=json.loads(gzip.decompress((R/'evidence/agent_runtime_cases.json.gz').read_bytes()))
    keys=[(i,pos) for i,(p,op,k) in enumerate(sites) for pos in ((False,True) if op=='CD' else (False,))]
    require([(c['index'],c['positive']) for c in cases]==keys,'Exhaustive ordered guarded census')
    require(all(len(c['duration'])==13 and all(type(v) is int and v>=0 for v in c['duration']) and c['duration'][0]>0 for c in cases),'Positive affine durations')
    info={'status':'STORED_CENSUS_AUDIT_ONLY','cases':len(cases),'symbolic_rules':sum(c['symbolic_steps'] for c in cases),'minimum_duration':min(c['duration'][0] for c in cases),'source_sha256':H(R/'machine/sites215.json'),'native_sha256':H(R/'machine/t215.native.tm')}
    require((info['cases'],info['symbolic_rules'],info['minimum_duration'])==(6209,1610781,10),'Pinned runtime census')
    return cases,info

def full_runtime(sites,T,stored,W):
    import symbolic_runtime as S
    mp={int(q):int(v) for q,v in read(R/'reference/transfer-parent/inputs/NATIVE_TO_LEGACY.json').items()}
    require(len(set(mp.values()))==len(mp),'Injective helper labels')
    for q in sorted({q for q,b in T}|{z for w,d,z in T.values()}):
        if q not in mp:mp[q]=max(mp.values())+1
    N={(mp[q],b):(w,d,mp[z]) for (q,b),(w,d,z) in T.items()}
    lemmas,blocks=S.prove_blocks(N);cases=[];rows=set();percase=[]
    for i,site in enumerate(sites):
        for positive in ((False,True) if site[1]=='CD' else (False,)):
            c=S.case(N,lemmas,site,positive)
            used=c.pop('rows');rows.update(used);c.pop('trace')
            c=dict(index=i,positive=positive,**c);cases.append(c)
            percase.append({'index':i,'positive':positive,'rows':sorted(used)})
        if i%500==0:print('Fresh runtime:',len(cases),'guarded cases',flush=True)
    require(json.loads(json.dumps(cases))==stored,'Fresh cases match every stored derivation summary')
    require(len(rows)==430,'All transition rows covered')
    blockref=read(R/'evidence/agent_runtime.json')['block_certificates']
    require(json.loads(json.dumps(blocks))==blockref,'Fresh exact block schemas')
    raw=(json.dumps(cases,separators=(',',':'))+'\n').encode()
    with gzip.GzipFile(filename=str(W/'fresh_runtime_cases.json.gz'),mode='wb',mtime=0) as f:f.write(raw)
    with gzip.GzipFile(filename=str(W/'fresh_runtime_rows.json.gz'),mode='wb',mtime=0) as f:f.write((json.dumps(percase,separators=(',',':'))+'\n').encode())
    return {'status':'ALL_NATURAL_RUNTIME_PASS','cases':len(cases),'symbolic_rules':sum(c['symbolic_steps'] for c in cases),'row_coverage':len(rows),'minimum_duration':min(c['duration'][0] for c in cases),'source_sha256':H(R/'machine/sites215.json'),'native_sha256':H(R/'machine/t215.native.tm'),'case_summaries_sha256':hashlib.sha256(raw).hexdigest(),'block_certificates':blocks}

def main():
    require(__debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'),'Run without -O or PYTHONOPTIMIZE')
    ap=argparse.ArgumentParser();ap.add_argument('--runtime',action='store_true');ap.add_argument('--out',type=Path);ap.add_argument('--no-manifest',action='store_true',help=argparse.SUPPRESS);a=ap.parse_args()
    if not a.no_manifest:
        files=read(R/'MANIFEST.json')['files']
        for x in files:
            p=R/x['path'];require(p.is_file() and p.stat().st_size==x['bytes'] and H(p)==x['sha256'],'Manifest: '+x['path'])
    W=a.out or Path(tempfile.mkdtemp(prefix='t215-replay-'))
    if a.out:W.mkdir(parents=True,exist_ok=False)
    started=time.monotonic();out={'target214_met':False,'candidate_states':215}
    sites,G,T,K,m,out['construction']=reconstruction();out['startup']=startup(sites,G,T,K,m,W)
    stored,out['stored_runtime']=stored_census(sites)
    scanner=read(R/'research/scanner/max5_206.sites.json')
    sg,_=L.graph_arithmetic(scanner);require(sg==G==L.graph_intervals(scanner),'Scanner experiment CFG')
    sm=L.metrics(L.tree(scanner));require(sm=={'dag_nodes':206,'leaf_occurrences':4775,'maximum_depth':42,'maximum_zero_run':5},'Scanner experiment metrics')
    out['scanner_experiment']={'status':'VALID_SOURCE_ONLY','metrics':sm,'smaller_binary_machine_claimed':False}
    # Optional only during packet assembly; final distribution includes both.
    import check_mathematics as M
    out['mathematics']=M.verify()
    import check_binary_evidence as B
    out['binary_evidence']=B.verify()
    research=subprocess.run([sys.executable,'-B',str(R/'research/short-transfer/reproduce.py')],check=True,stdout=subprocess.PIPE,text=True)
    out['short_transfer_research']=json.loads(research.stdout)
    require(out['short_transfer_research']['status']=='RESEARCH_RECONSTRUCTION_PASS','Short-transfer reconstruction')
    print('PASS: exact construction, source CFGs, full blank frame, logical certificates, binary evidence, and stored runtime census',flush=True)
    if a.runtime:out['runtime']=full_runtime(sites,T,stored,W)
    out['status']='FULL_REPLAY_PASS' if a.runtime else 'FINITE_REPLAY_PASS';out['seconds']=time.monotonic()-started
    dump(W/'replay.json',out);print(json.dumps({k:v for k,v in out.items() if k not in ('mathematics','binary_evidence','runtime')},indent=2));print('Receipts:',W)
if __name__=='__main__':main()
