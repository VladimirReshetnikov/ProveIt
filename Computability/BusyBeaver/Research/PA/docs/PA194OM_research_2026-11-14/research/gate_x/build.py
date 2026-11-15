#!/usr/bin/env python3
"""Rebuild the exploratory G_X physical table using only bundled inputs.

The symbolic runtime validator uses arithmetic-box oracles.  Its successful
contracts are not a complete blank-start verification or an independent literal
proof.  See README.txt for the precise research status.
"""
from pathlib import Path
import argparse, collections, hashlib, json, sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c
import support as s
import engine_foldscreen as f

def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
def dump(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--grammar',type=Path,default=HERE/'grammar.json')
    ap.add_argument('--out',type=Path,default=HERE/'rebuilt_initial198')
    args=ap.parse_args();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
    nodes={k:tup(v)for k,v in json.loads((HERE/'nodes.json').read_text()).items()}
    fixed={k:v for k,v in s.read_table(HERE/'inputs/primary.raw.native.tm').items()if k[0]<1300}
    fixed[164,1]=(1,True,114)
    for q,b,a in json.loads((HERE/'inputs/h_shift_edits.json').read_text()):fixed[q,b]=tuple(a)
    c.raw_nodes=lambda:nodes;c.machine=lambda:(fixed,[])
    c.MACROS.update(json.loads((HERE/'macro_additions.json').read_text()))
    inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    grammar=c.read_grammar(args.grammar);raw,index,shape=c.build(grammar)
    incoming=collections.defaultdict(set)
    for w,d,n in raw.values():incoming[n].add((w,d))
    opportunities=[o for o in f.opportunities(raw)
                   if incoming[o[0]]=={(0,True)} and incoming[o[1]]=={(1,True)}]
    matching=f.matching(opportunities);choices={(a,b):o for a,b,o in opportunities}
    folds=[[a,b,[o[0]for o in choices[a,b]]]for a,b in matching]
    rows,aliases=s.apply_folds(raw,folds)
    local=s.check_local_folds(raw,rows,aliases,folds)
    sites,instructions,contracts=c.source(grammar)
    assert [list(x)for x in instructions]==json.loads((HERE/'instructions.json').read_text()),'source graph changed'
    print('raw',len(raw)//2,'fixed',len(fixed)//2,'readers',len(shape),
          'folds',len(folds),'working',len(rows)//2,flush=True)
    print('sites',len(sites),'contracts',len(contracts),flush=True)
    validation=c.validate(rows,contracts);assert validation['ok'],validation
    print(validation,flush=True)
    dense,labels=s.dense_table(rows,len(rows)//2)
    for name,obj in [('raw.native.tm',raw),('machine.native.tm',rows),('machine.tm',dense)]:
        (out/name).write_text(s.table_text(obj))
    for name,obj in [('nodes.json',nodes),('sites.json',sites),('instructions.json',instructions),
                     ('folds.json',folds),('local_folds.json',local),('labels.json',labels),
                     ('validation.json',validation)]:dump(out/name,obj)
    (out/'grammar.json').write_bytes(args.grammar.read_bytes())
    receipt=dict(status='PASS_RESEARCH_RUNTIME_CHECK',raw_states=len(raw)//2,
        fixed_states=len(fixed)//2,reader_states=len(shape),folds=len(folds),working_states=len(rows)//2,
        source_sites=len(sites),source_outcomes=len(contracts),runtime=validation,
        arithmetic_box_oracles=True,complete_blank_start_checked=False,
        independent_literal_runtime_checked=False,physical_ConPA_theorem_claimed=False,
        native_sha256=sha(out/'machine.native.tm'),dense_sha256=sha(out/'machine.tm'),
        source_graph_equal_to_supplied_GX=True)
    dump(out/'receipt.json',receipt)
    # Reproduce the grammar-search input with the actual available fixed states.
    leaves=set();ts=[];ids={}
    def st(t):
        if t in ids:return ids[t]
        if c.isnode(t):v=(1,st(t[0]),st(t[1]),0)
        else:
            q=-1 if t==('leaf','breakTo',1)else c.MACROS[t]
            leaves.add((q,t));v=(0,q,-1,-1)
        k=len(ts);ids[t]=k;ts.append(v);return k
    root=st(grammar);fixedqs=sorted({q for q,b in fixed});lines=[str(len(fixedqs))]
    for q in fixedqs:
        lines.append(' '.join(map(str,[q,*fixed[q,0],*fixed[q,1]])).replace('True','1').replace('False','0'))
    lines+=['1',f'0 {len(ts)} {root}']+[' '.join(map(str,t))for t in ts]
    (out/'seed.txt').write_text('\n'.join(lines)+'\n')
    def paths(t,p=''):
        if isinstance(t,str):return paths(nodes[t],p)
        if c.isnode(t):return paths(t[0],p+'0')+paths(t[1],p+'1')
        return [(p,t)]
    attrs=[]
    for q,t in sorted(leaves):
        ps=paths(t);h=max(len(p)for p,v in ps);left=len(ps[0][0])
        m=max(len(z)for p,v in ps for z in p.split('1'))
        mi=max([len(z)for p,v in ps if v[1]=='inc'for z in p.split('1')]+[0])
        inc_first=ps[0][1][1]=='inc'
        attrs.append(f'{q} {h} {left} {m} {mi} {int(inc_first)}')
    (out/'leaf_attrs.txt').write_text(str(len(attrs))+'\n'+'\n'.join(attrs)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
