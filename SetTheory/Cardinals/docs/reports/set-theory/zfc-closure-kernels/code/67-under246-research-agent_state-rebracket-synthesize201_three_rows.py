#!/usr/bin/env python3
"""Lazy full-table synthesis at q218/0, q256/1, q244/1 in a 201-node layout.

Failures certify only rejection by the named affine system at its stated fuel,
not literal incorrectness or a state lower bound. Unknown rows trigger branching
when first read; a previously completed trace cannot read a later-assigned row.
"""
import sys,json,time,itertools,hashlib,gzip,argparse
from pathlib import Path
from search_repair import HERE,compiler,cases,run
from search_rotated_merges import macro_check
sys.path.insert(0,str(HERE.parents[1]/'root_search'))
import compile201

class NeedRow(Exception):pass
class Incomplete(Exception):pass
class Partial(dict):
    def __init__(self,t,keys):super().__init__(t);self.keys=set(keys);self.assigned={}
    def __getitem__(self,k):
        if k in self.keys:
            if k not in self.assigned:raise NeedRow(k)
            return self.assigned[k]
        return super().__getitem__(k)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-nodes',type=int,default=2000000)
    ap.add_argument('--extra-218-one',action='store_true')
    ap.add_argument('--extra-256-zero',action='store_true')
    args=ap.parse_args()
    began=time.monotonic();n,r,t=compile201.build()
    t['243',0]=(0,'R','113');t['243',1]=(1,'R','218')
    keys=[('218',0),('256',1),('244',1)]
    if args.extra_218_one:keys.append(('218',1))
    if args.extra_256_zero:keys.append(('256',0))
    stem='synthesis201_'+str(len(keys))+'_rows'
    if len(keys)==3:stem='synthesis201_three_rows'
    states=sorted({q for q,b in t},key=int)
    actions=list(itertools.product((0,1),('L','R'),states+['254']))
    cc=list(cases(n,r))
    preface=[]
    if args.extra_218_one:
        # These baseline traces use q218/1 while avoiding the other three
        # synthesis rows. Fixing their semantics first reduces fruitless forks.
        preface=[742,1191,1289,1497,2374,3168,3266,3783,4161,4257,4318,4416,4589,4791,4887,5124,5220,5281,5379,5852]
    order=list(dict.fromkeys(preface+[1166,708,3924,3925,3959,5655]+list(range(len(cc)))))
    u=Partial(t,keys);tree=[];counts=dict(calls=0,affine_runs=0,reject_nodes=0,split_nodes=0,covered=0);survivors=[]
    action_ids={k:i for i,k in enumerate(actions)}

    def dfs(index):
        counts['calls']+=1
        if counts['calls']>args.max_nodes:raise Incomplete('node limit')
        if counts['calls']%10000==0:
            print('progress',counts,'seconds',round(time.monotonic()-began,3),flush=True)
        node=len(tree);tree.append(None)
        while index<len(order):
            i=order[index]
            try:counts['affine_runs']+=1;run(u,cc[i])
            except NeedRow as e:
                k=e.args[0];ki=keys.index(k)
                counts['split_nodes']+=1;children=[]
                tree[node]=dict(split=ki,children=children)
                for action in actions:
                    u.assigned[k]=action
                    children.append(dfs(index))
                del u.assigned[k]
                return node
            except (AssertionError,KeyError) as e:
                counts['reject_nodes']+=1
                count=len(actions)**(len(keys)-len(u.assigned));counts['covered']+=count
                tree[node]=dict(reject=i,message=str(e),completions=count)
                return node
            index+=1
        # No unresolved row can affect any source guard. Fill arbitrary actions.
        candidate=dict(t);candidate.update(u.assigned)
        macro_check(candidate)
        patch=[dict(state=q,read=b,action=list(candidate[q,b])) for q,b in keys]
        survivors.append(patch);print('PROVISIONAL PASS',patch,flush=True)
        (HERE/f'synthesized201_245_{len(survivors)}.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {s}\n' for (q,b),(w,d,s) in sorted(candidate.items(),key=lambda kv:(int(kv[0][0]),kv[0][1]))))
        count=len(actions)**(len(keys)-len(u.assigned));counts['covered']+=count
        tree[node]=dict(accept=len(survivors)-1,completions=count)
        return node

    status='COMPLETE'
    try:root=dfs(0)
    except Incomplete as e:status=str(e);root=0
    report=dict(status=status,scope=__doc__,rows=keys,actions=actions,cases=len(cc),order=order,fuel=1500,counts=counts,total_family=len(actions)**len(keys),survivors=survivors,seconds=time.monotonic()-began,root=root,tree=tree)
    raw=json.dumps(report,separators=(',',':')).encode()+b'\n'
    with gzip.open(HERE/(stem+'.json.gz'),'wb') as f:f.write(raw)
    summary={k:v for k,v in report.items() if k not in ('actions','order','tree')};summary['raw_sha256']=hashlib.sha256(raw).hexdigest()
    (HERE/(stem+'_summary.json')).write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2),flush=True)

if __name__=='__main__':main()
