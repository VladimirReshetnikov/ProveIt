#!/usr/bin/env python3
"""Independently audit literal decoder rotations and their source CFG.

This checker does not import the discovery program, its prefix map, or its
source manipulation utilities. It reconstructs every internal-prefix entry
from the literal table, checks closure and incoming edges, and recomputes
the complete ordinal CFG after every rotation. It deliberately distinguishes
these structural results from the final origin-detector admissibility test.
"""
from pathlib import Path
from collections import defaultdict
import argparse, hashlib, json

def require(ok, message):
    if not ok: raise ValueError(message)

def read_table(path):
    rows={}; start=[]
    for line in Path(path).read_text().splitlines():
        if line.startswith('#! start '):start.append(int(line[9:]));continue
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        require((q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R'),'bad table row')
        rows[q,b]=w,1 if d=='R'else-1,t
    require(start==[0],'start is not zero')
    return rows

def source_info(rows):
    leaves={p:(o,a)for p,o,a in rows};require(len(leaves)==len(rows),'duplicate leaf')
    branch={};interval={};boundary={};serial=[];subtree={}
    def visit(p):
        lo=len(serial)
        if p in leaves:
            op,arg=leaves[p];serial.append([p,op,arg]);subtree[p]=(op,arg)
            boundary[p]=(1 if op=='CD' else arg if op=='CB' else 0,
                         arg if op=='CC' else 0, op=='CH')
        else:
            # Finite depth prevents an incomplete tree from recursing forever.
            require(len(p)<=max_depth,'incomplete prefix tree')
            visit(p+'0');visit(p+'1');branch[p]=(p+'0',p+'1')
            x,y=boundary[p+'0'],boundary[p+'1']
            boundary[p]=(max(x[0]-1,y[0],0),max(x[1],y[1]-1,0),x[2]or y[2])
            subtree[p]=(subtree[p+'0'],subtree[p+'1'])
        interval[p]=lo,len(serial)
    max_depth=max(len(p)for p in leaves);visit('');require(serial==rows,'noncanonical source')
    size=len(rows);cfg=[]
    def target(p,edge,number):
        positions=[j for j,b in enumerate(p)if b==edge]
        require(len(positions)>=number,'unbound branch')
        ancestor=p[:positions[-number]]
        return interval[ancestor][0 if edge=='1'else 1]%size
    for i,(p,op,arg)in enumerate(rows):
        if op=='CI':out=((i+1)%size,)
        elif op=='CD':out=(target(p,'0',1),(i+1)%size)
        elif op=='CB':out=(target(p,'0',arg),)
        elif op=='CC':out=(target(p,'1',arg),)
        elif op=='CH':out=()
        else:raise ValueError('bad opcode')
        cfg.append((op,arg,out))
    metrics={'primitives':size,'dag_nodes':len(set(subtree.values())),
             'maximum_depth':max_depth,
             'maximum_zero_run':max(len(v)for p in leaves for v in p.split('1'))}
    return branch,boundary,cfg,metrics

def prefix_binding(table, prefixes):
    bound={};max_steps=0
    for word in prefixes:
        q,h=84,0;known={-1:1,**dict(enumerate(map(int,word)))}
        for steps in range(1000):
            if h==len(word):break
            require(h in known,('prefix reads opaque cell',word,q,h))
            b=known[h];w,d,q=table[q,b]
            require(w==b,('prefix overwrites a cell',word,h))
            h+=d
        else:raise ValueError(('prefix does not finish',word))
        bound[word]=q;max_steps=max(max_steps,steps)
    return bound,max_steps

def rotate_addresses(rows, roots, side):
    def transform(path):
        for pre in roots:
            if path.startswith(pre):
                s=path[len(pre):]
                # Leaves cannot equal an outer or its inner branch node.
                if side==0:
                    if s.startswith('00'):s='0'+s[2:]
                    elif s.startswith('01'):s='10'+s[2:]
                    else:require(s.startswith('1'),'bad left rotation leaf');s='11'+s[1:]
                else:
                    if s.startswith('0'):s='00'+s[1:]
                    elif s.startswith('10'):s='01'+s[2:]
                    else:require(s.startswith('11'),'bad right rotation leaf');s='1'+s[2:]
                return pre+s
        return path
    return [[transform(p),op,arg]for p,op,arg in rows]

def audit(base_table,base_source,recipe,final_table,final_source):
    table=read_table(base_table);rows=json.loads(Path(base_source).read_text())
    _,_,original_cfg,original_metrics=source_info(rows)
    records=[]
    for step,(p,q,side)in enumerate(json.loads(Path(recipe).read_text())):
        print('AUDIT_STEP',step,p,q,side,flush=True)
        require(side in(0,1),'invalid rotation side')
        branches,bd,cfg,metrics=source_info(rows)
        binding,max_steps=prefix_binding(table,branches)
        roots=sorted(x for x,v in binding.items()if v==p)
        require(roots,'outer state has no source occurrence')
        require(all(not a.startswith(b)for a in roots for b in roots if a!=b),'nested occurrences')
        require(all(table[x,b][:2]==(b,1)for x in(p,q)for b in(0,1)),'non-pure decoder')
        require(table[p,side][2]==q,'wrong inner state')
        incoming={key for key,act in table.items()if act[2]==q}
        require(incoming=={(p,side)},('inner has another physical entry',incoming))
        for word in roots:
            require(binding[word+str(side)]==q,'inner prefix binding disagrees')
            factors=[word+'00',word+'01',word+'1']if side==0 else [word+'0',word+'10',word+'11']
            require(all(bd[a]==(0,0,False)for a in factors),'a source factor is not closed')
        if side==0:
            a,b,c=table[q,0][2],table[q,1][2],table[p,1][2]
            edits={(p,0):(0,1,a),(p,1):(1,1,q),(q,0):(0,1,b),(q,1):(1,1,c)}
        else:
            a,b,c=table[p,0][2],table[q,0][2],table[q,1][2]
            edits={(p,0):(0,1,q),(p,1):(1,1,c),(q,0):(0,1,a),(q,1):(1,1,b)}
        table.update(edits);rows=rotate_addresses(rows,roots,side)
        new_branches,new_bd,new_cfg,new_metrics=source_info(rows)
        require(new_cfg==original_cfg,'complete source CFG changed')
        # Fresh literal prefix derivations are repeated after every edit,
        # rather than trusting a transported state-to-prefix dictionary.
        new_binding,new_max=prefix_binding(table,new_branches)
        records.append({'step':step+1,'outer':p,'inner':q,'side':side,
                        'source_occurrences':roots,'internal_prefixes':len(new_binding),
                        'maximum_prefix_steps':new_max,'metrics':new_metrics})
    expected_source=json.loads(Path(final_source).read_text())
    require(rows==expected_source,'reconstructed final source differs')
    require(table==read_table(final_table),'reconstructed rotated table differs')
    _,_,final_cfg,metrics=source_info(rows)
    require(final_cfg==original_cfg,'final CFG differs')
    return {'status':'INDEPENDENT_ROTATION_SOURCE_AUDIT_PASS',
            'rotations':len(records),'base_metrics':original_metrics,'final_metrics':metrics,
            'source_cfg_primitives_checked_per_stage':len(original_cfg),
            'seven_zero_detector_source_bound_satisfied':metrics['maximum_zero_run']<=6,
            'records':records,
            'scope':'Literal decoder/source reconstruction and exact ordinal CFG only. '
                    'Whole-runtime and startup correctness are separate obligations.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('base_table');p.add_argument('base_source')
    p.add_argument('recipe');p.add_argument('final_table');p.add_argument('final_source')
    p.add_argument('--output',required=True);args=p.parse_args()
    report=audit(args.base_table,args.base_source,args.recipe,args.final_table,args.final_source)
    report['input_sha256']={k:hashlib.sha256(Path(getattr(args,k)).read_bytes()).hexdigest()
                           for k in('base_table','base_source','recipe','final_table','final_source')}
    Path(args.output).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()if k!='records'},indent=2))

if __name__=='__main__':main()
