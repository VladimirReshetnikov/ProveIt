#!/usr/bin/env python3
"""Independent K220 stored-runtime, four-block, source, fold, and startup audit.

Adapted from ProveIt's pinned K221 audit221.py and check224.py.  Existing
MIT No Attribution notices apply.  This audits stored proof integrity and
coverage; it does not replace the fresh 6167-case symbolic induction replay.
The optional fold check is restricted to source-decoder entries.  No fold
equivalence on arbitrary initial tapes is claimed.
"""
from pathlib import Path
import argparse,json,hashlib,sys,collections

TABLE_SHA='4466ec4f947a9c5112397c30ca25b0e70e3ac39ee54878b3e4493a0297d732e4'
SOURCE_SHA='837e92d7b1c107330f160f654f6c36ff0b03dfbf6bc2b89c6f782eb7db4c4ce7'
ENGINE_SHA='c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145'
HELPER_SHA='0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'
DRIVER_SHA='a64e0f5622c8c6c6f23fb1755c0473e81481ef0c30e795d23fad67bc3425432b'
MAPPING_SHA='26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf'
BASE_SOURCE_SHA='691684ec948c972bf67727d6d4cd1181a90a9203644ee3db3eae363280e3fac9'
SOURCE_CHECKER_SHA='bd65fb0f8e89935f8b3651d7e76f01e0e378b4cb995af9d5f46ab11d5ffef393'
CASES_SHA='6c2b15b8e3f7b35f3eb37f87510ba3c51a11b9703d42f995f6a695381e12e381'

def need(x,message):
    if not x:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def source_dag(sites):
    ids={};by_path={};internal=set()
    def intern(x):
        if x not in ids:ids[x]=len(ids)
        return ids[x]
    for p,op,arg in sites:
        by_path[p]=intern(('L',op,arg));internal.update(p[:i]for i in range(len(p)))
    for p in sorted(internal,key=len,reverse=True):by_path[p]=intern(('N',by_path[p+'0'],by_path[p+'1']))
    return len(ids),internal

def normalize(word):
    out=[]
    for bit,constant,variable in word:
        if out and out[-1][0]==bit:
            b,c,v=out.pop();out.append((b,c+constant,v+variable))
        else:out.append((bit,constant,variable))
    return out

def exact_blocks(table,stored):
    """Prove the four schemas by literal rows and one explicitly checked self-loop.

    Each token (bit,c,v) has length c+v*n for arbitrary natural n.  The sole
    variable token is traversed by a self-loop, including its n=0 case.
    Remaining tokens are one cell each.  Only represented cells are touched.
    """
    B=[(0,1,0),(1,1,1)];C=[(1,1,0),(0,1,0),(1,0,1)]
    specs=[(73,1,'B','B',[(0,1,0),(1,1,0),(1,0,1)]),
           (95,1,'B','C',[(0,1,0),(1,1,0),(1,0,1)]),
           (48,-1,'B','B',[(1,1,0),(1,0,1),(0,1,0)]),
           (112,-1,'C','B',[(1,0,1),(0,1,0),(1,1,0)])]
    need([(x['entry'],x['direction'],x['before'],x['after'])for x in stored]
         ==[(q,d,a,b)for q,d,a,b,t in specs],'Four block signatures')
    reports=[]
    for rec,(entry,direction,before,after,tokens)in zip(stored,specs):
        target=B if after=='B'else C
        input_word=B if before=='B'else C
        if direction==-1:target=list(reversed(target));input_word=list(reversed(input_word))
        need(normalize(tokens)==normalize(input_word),'Block input word identity')
        q=entry;written=[];trace=[];c=v=0
        for bit,constant,variable in tokens:
            write,move,nxt=table[q,bit]
            need(move==direction,'Block scan direction')
            row=[q,bit,write,move,nxt]
            if variable:
                need((constant,variable)==(0,1)and nxt==q,'Unbounded token is not a self-loop')
                trace.append(['unary',row,[0,0,1]+[0]*10])
            else:
                need(constant==1,'Literal token is not one cell')
                trace.append(['literal',row])
            written.append((write,constant,variable));c+=constant;v+=variable;q=nxt
        need(q==entry and(c,v)==(2,1),'Block state or duration formula')
        need(normalize(written)==normalize(target),'Block output word identity')
        need(rec['steps']=='v+2'and rec['arbitrary_contexts']is True and rec['trace']==trace,
             'Stored block differs from independent exact-row derivation')
        reports.append({'entry':entry,'direction':direction,'before':before,'after':after,
                        'duration':[2,1],'trace':trace,'arbitrary_exterior_untouched':True})
    return reports

def prefixes(table,internal):
    relation={}
    for prefix in sorted(internal):
        tape={-1:1,**{i:int(b)for i,b in enumerate(prefix)}};before=dict(tape);q=84;h=0
        for tick in range(20000):
            if h==len(prefix):break
            need(h in tape and q!=254,'Prefix decoder touches unknown exterior or halts')
            w,d,q=table[q,tape[h]];tape[h]=w;h+=d
        else:raise ValueError('Prefix decoder bound')
        need(tape==before,'Prefix decoder changes its input word')
        relation[prefix]=q
    return relation

def check_fold(old,new,internal):
    phi=lambda q:171 if q==202 else q
    expected={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in old.items()if q!=202}
    expected[171,0]=(0,-1,7)
    need(new==expected,'Candidate is not the specified 202-to171 fold')
    oldrel=prefixes(old,internal);newrel=prefixes(new,internal)
    need(all(newrel[p]==phi(q)for p,q in oldrel.items()),'Decoder state relation')
    paths={q:[p for p,z in oldrel.items()if z==q]for q in(171,202)}
    need(all(paths.values())and all(p.endswith('1')for p in paths[171])
         and all(p.endswith('0')for p in paths[202]),'Source predecessor tags')
    blocks=[]
    for q,tag in[(171,1),(202,0)]:
        for bit in(0,1):
            cells={-1:tag,0:bit};wanted=dict(cells);w,d,z=old[q,bit];wanted[0]=w
            state=171;h=0;trace=[];steps=3 if bit==0 else 1
            for _ in range(steps):
                need(h in cells and state!=254,'Fold touches arbitrary exterior or halts')
                read=cells[h];ww,dd,zz=new[state,read]
                trace.append([state,h,read,ww,dd,zz]);cells[h]=ww;h+=dd;state=zz
            need((state,h,cells)==(phi(z),d,wanted),'Fold endpoint or whole tape')
            blocks.append({'old_state':q,'read':bit,'predecessor_tag':tag,'steps':steps,'trace':trace})
    return {'status':'SOURCE_PREFIX_RESTRICTED_FOLD_PASS','state_map':{'202':171},
            'source_paths':paths,'blocks':blocks,'source_node_occurrences':len(oldrel),
            'scope':'Only valid source-decoder entries. Startup is checked separately; no arbitrary-initial-tape theorem.'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--sites',type=Path,required=True)
    ap.add_argument('--runtime',type=Path,required=True);ap.add_argument('--baseline',type=Path,required=True)
    ap.add_argument('--driver',type=Path,required=True);ap.add_argument('--prefold',type=Path)
    ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    H=a.baseline/'portable/runtime'
    need(sha(H/'check224.py')==SOURCE_CHECKER_SHA,'Independent source/parser implementation pin')
    sys.path.insert(0,str(H));import check224 as c
    T,st,halt,Q=c.parse(a.table)
    need(sha(a.table)==TABLE_SHA and sha(a.sites)==SOURCE_SHA,'Pinned K220 inputs')
    need((st,halt,len(Q),len(T))==(0,254,220,440),'Literal state/row census')
    need(sha(a.baseline/'machine/sites221.json')==BASE_SOURCE_SHA,'Baseline source pin')
    r=json.loads((a.runtime/'runtime.json').read_text());cases=json.loads((a.runtime/'cases.json').read_text())
    need(sha(a.runtime/'cases.json')==CASES_SHA,'Pinned complete guarded-case certificate bytes')
    need(r['status']=='ALL_PRIMITIVE_INTERFACES_PROVED'and r['debug_enabled']is True,'Incomplete or optimized runtime proof')
    for field,path,digest in [('table_sha256',a.table,TABLE_SHA),
        ('sites_sha256',a.sites,SOURCE_SHA),('driver_sha256',a.driver,DRIVER_SHA)]:
        need(r[field]==sha(path)==digest,('Provenance hash',field))
    dependencies={'portable/build221.py':'3359e8b40fefb162ca4aa1d5c5a99a368a937ec61f761c3ac6f26d573766acba',
        'portable/source_language.py':'4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f',
        'portable/runtime/vendor/symbolic_runtime.py':ENGINE_SHA,
        'portable/runtime/vendor/independent_runtime.py':HELPER_SHA,
        'portable/runtime/reference_results/legacy_mapping.json':MAPPING_SHA}
    need(r['dependencies']==dependencies,'Runtime dependency manifest')
    for name,digest in dependencies.items():need(sha(a.baseline/name)==digest,('Dependency bytes',name))
    mp0={int(q):int(z)for q,z in json.loads((H/'reference_results/legacy_mapping.json').read_text()).items()}
    need(Q|{254}<=set(mp0),'Mapping is undefined on a candidate state')
    mp={q:mp0[q]for q in Q|{254}}
    need(len(set(mp.values()))==221 and(mp[0],mp[84],mp[254])==(95,96,254),'Restricted runtime label bijection')
    legacy={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in T.items()}
    need(len(legacy)==440,'Runtime relabeling collision')
    todo=[0];reachable={0}
    for q in todo:
        for bit in(0,1):
            z=T[q,bit][2]
            if z!=254 and z not in reachable:reachable.add(z);todo.append(z)
    need(reachable==Q,'Graph-reachable working-state census')
    S,G,M=c.source_graph(a.sites);B,BG,BM=c.source_graph(a.baseline/'machine/sites221.json')
    need([x[1:]for x in S]==[x[1:]for x in B]and G==BG,'Source opcode word and complete guarded CFG')
    dag,internal=source_dag(S)
    metric={'dag_nodes':dag,'leaf_occurrences':len(S),'maximum_depth':M['maximum_depth'],'maximum_zero_run':M['maximum_zero_run']}
    need(metric==r['source_metrics']=={'dag_nodes':208,'leaf_occurrences':4744,'maximum_depth':38,'maximum_zero_run':6},'Independent source census')
    expected=[(i,p)for i,(_,op,arg)in enumerate(S)for p in((False,True)if op=='CD'else(False,))]
    need(len(cases)==len(expected)==r['cases']==r['expected_cases']==6167,'Guarded case count')
    need([(x['index'],x['positive'])for x in cases]==expected,'Exact ordered guarded case coverage')
    for x in cases:
        need(type(x['index'])is int and type(x['positive'])is bool,'Case identifier types')
        need(type(x['symbolic_steps'])is int and 0<x['symbolic_steps']<4000,'Symbolic construction bound')
        need(len(x['duration'])==13 and all(type(v)is int and v>=0 for v in x['duration'])and x['duration'][0]>0,
             'Nonnegative affine duration or positive progress')
        need(len(x['motion'])==13 and all(type(v)is int for v in x['motion']),'Affine head displacement')
        need(set(x['kinds'])<={'literal','unary','list'}and all(type(v)is int and v>0 for v in x['kinds'].values())
             and sum(x['kinds'].values())==x['symbolic_steps'],'Symbolic rule classification')
    need(sum(x['symbolic_steps']for x in cases)==r['symbolic_steps']==1516421,'Total symbolic rules')
    need(min(x['duration'][0]for x in cases)==r['minimum_actual_steps']==13,'Positive duration minimum')
    need(r['working_states']==220 and r['transition_rows']==440,'Receipt census')
    need(r['directly_used_native_rows']==[list(k)for k in sorted(T)],'Full row usage receipt')
    blocks=exact_blocks(legacy,r['block_schemas'])
    q,h,ones,used=c.execute(T,0,254,409835);wanted,logical,physical=c.expected_frame()
    need((q,h,ones)==(84,-5,wanted),'Fresh complete blank startup')
    need(len(ones)==351 and logical==[3,0,0,0,3,0,0,0,0],'Startup seed')
    result={'status':'INDEPENDENT_K220_RUNTIME_INTEGRITY_COVERAGE_BLOCKS_SOURCE_AND_STARTUP_PASS',
        'working_states':220,'transition_rows':440,'graph_reachable_working_states':220,
        'guarded_cases':6167,'symbolic_steps':1516421,'minimum_duration_constant':13,
        'source_metrics':metric,'source_opcode_word_and_guarded_CFG_equal_K221':True,
        'blocks_independently_rederived':blocks,'label_bijection_checked':True,
        'startup':{'steps':409835,'state':84,'head':-5,'one_cells':351,'header':176,'extra_gap':117,
                   'logical_seed':logical,'physical_registers':physical,'spares':[1]*167,'all_other_cells':0},
        'table_sha256':TABLE_SHA,'source_sha256':SOURCE_SHA,'runtime_receipt_sha256':sha(a.runtime/'runtime.json'),
        'cases_sha256':sha(a.runtime/'cases.json'),'auditor_sha256':sha(Path(__file__)),
        'source_checker_sha256':sha(Path(c.__file__)),'assertions_required':False,
        'scope':'Stored proof integrity and exact case coverage; four literal-table unary/list schemas are independently rederived. The full fresh symbolic induction replay remains a distinct certificate. Exact initialized tape and source semantics are checked here. No proof-assistant kernel endpoint is claimed.'}
    if a.prefold:
        old,ost,oh,oq=c.parse(a.prefold);need((ost,oh,len(oq))==(0,254,221),'Prefold table census')
        result['fold']=check_fold(old,T,internal);result['prefold_sha256']=sha(a.prefold)
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in('blocks_independently_rederived','startup','fold')},indent=2))
    if a.prefold:print('Source-prefix fold:',result['fold']['status'])

if __name__=='__main__':main()
