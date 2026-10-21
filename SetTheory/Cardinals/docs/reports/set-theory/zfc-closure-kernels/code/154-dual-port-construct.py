#!/usr/bin/env python3
"""Deterministically reconstruct the two new 219-state MP-return variants.

This is source binding and literal construction, not a runtime theorem.
The ordinary mathematical command proof is in the accompanying report.
"""
from pathlib import Path
import argparse,hashlib,json,sys

TABLE_SHA='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
SOURCE_SHA='0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
CONFIG={
 'no_push_copy':{'target':114,'leaves':4725,'cases':6142,
  'table_sha256':'530f9866566929681bdf783fe21ce044e0b81047c6bdd59df54cca70102296e8',
  'source_sha256':'9f504e5fe8033407b34407168b0ca4f775b30a21b9e8ac3181f0cd09aa4c9e3e'},
 'no_push_cache':{'target':130,'leaves':4721,'cases':6137,
  'table_sha256':'ae0cc5d730cdb39da13e23eec725f48d96a0a254c1b9402521af30edfb8fc3e5',
  'source_sha256':'e39c808c47da6c47d6c2fdafd1cb6a0e33004bf1c5daa141a8dbdbf9b3f297b3'},
}
def sha(x):return hashlib.sha256(x).hexdigest()
def require(ok,reason):
    if not ok:raise ValueError(reason)
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')

def run_source_cases(s,old,new,kind):
    def evaluator(n,regs):
        # The right-hand sentinel is reached only on normal macro completion.
        rows=s.sites((n,('CH',None)));graph=s.graph_arithmetic(rows)[0]
        assert graph==s.graph_intervals(rows)
        r=list(regs);i=0
        for ticks in range(100000):
            effect,targets=graph[i];op=effect[0]
            if op=='halt':return r,ticks
            if op=='increment':r[effect[1]]+=1;i=targets[0]
            elif op=='decrement':
                j=effect[1];positive=r[j]>0
                if positive:r[j]-=1
                i=targets[int(positive)]
            else:i=targets[0]
        raise ValueError('Source regression exceeded its finite step cap')
    mp=s.subtree(new,'1111');count=0
    def pair(a,b):return(a+b)*(a+b+1)//2+b
    for t in range(6):
        for d in range(6):
            implication=4*pair(t,d)
            for h in sorted({0,1,implication,max(0,implication-1),implication+1}):
                for w in (0,1,3,6):
                    before=[7,t,w,0,d,h,0,0,9]
                    after,ticks=evaluator(mp,before)
                    want=before.copy();want[1]=want[5]=0
                    if implication==h:
                        if kind=='no_push_copy':want[1]=d
                        else:want[4]=0;want[5]=d
                    require(after==want,('MP source contract regression',kind,before,after,want))
                    count+=1
    return {'status':'FINITE_SOURCE_MP_CONTRACT_PASS','cases':count,
            'scope':'Finite regression of the complete changed MP source block; the uniform proof is in the report.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline219',type=Path,required=True)
    ap.add_argument('--baseline221',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();require(__debug__,'Do not run Python with -O')
    sys.path.insert(0,str(a.baseline221/'portable'))
    import source_language as s,build221 as b
    raw=(a.baseline219/'machine/k219.native.tm').read_bytes()
    sr=(a.baseline219/'machine/sites219.json').read_bytes()
    require(sha(raw)==TABLE_SHA and sha(sr)==SOURCE_SHA,'Pinned predecessor bytes differ')
    old=s.tree(json.loads(sr));table=b.read_table(raw)
    # This is the successful MP arm: the last ordinary push-D macro.
    old_return=s.subtree(old,'111111')
    require(len(s.sites(old_return))==26,'Unexpected predecessor return macro')
    copy=s.subtree(old,'1111111')
    require(len(s.sites(copy))==7,'Unexpected copy-D macro')
    cache=(('CD',4),(('CI',5),('CC',2)))
    a.output.mkdir(parents=True,exist_ok=True);receipts=[]
    for kind,node in [('no_push_copy',copy),('no_push_cache',cache)]:
        cfg=CONFIG[kind];new=s.replace(old,'111111',node);sites=s.sites(new)
        require(s.graph_arithmetic(sites)[0]==s.graph_intervals(sites),'CFG resolvers disagree')
        metrics=s.metrics(new)
        require(metrics=={'dag_nodes':206,'leaf_occurrences':cfg['leaves'],
          'maximum_depth':38,'maximum_zero_run':6},'Changed source metrics differ')
        U=dict(table);require(U[164,1]==(1,1,98),'Predecessor row164/1 differs')
        U[164,1]=(1,1,cfg['target'])
        groups,paths=b.decoder_map(U,new)
        require(sum(len(ns)for ns in groups.values())==184,'Decoder interior census')
        require(sum(len(ns)-1 for ns in groups.values())==15,'Decoder alias census')
        encoded=b.table_bytes(U);source=s.compact(sites)
        require(sha(encoded)==cfg['table_sha256'],'Reconstructed table identity')
        require(sha(source)==cfg['source_sha256'],'Reconstructed source identity')
        require(sum(2 if op=='CD'else 1 for pc,op,j in sites)==cfg['cases'],'Guard census')
        folder=a.output/kind;folder.mkdir(exist_ok=True)
        (folder/'candidate.native.tm').write_bytes(encoded);(folder/'sites.json').write_bytes(source)
        receipt={'variant':kind,'status':'SOURCE_AND_LITERAL_TABLE_BINDING_PASS',
          'working_states':len(U)//2,'rows':len(U),'source_metrics':metrics,
          'changed_native_row':[164,1,1,'R',cfg['target']],
          'replaced_source_path':'111111','primitive_cases':cfg['cases'],
          **cfg,'source_regression':run_source_cases(s,old,new,kind)}
        dump(folder/'construction.json',receipt);receipts.append(receipt)
        print(kind,receipt['status'],flush=True)
    dump(a.output/'construction.json',receipts)
if __name__=='__main__':main()
