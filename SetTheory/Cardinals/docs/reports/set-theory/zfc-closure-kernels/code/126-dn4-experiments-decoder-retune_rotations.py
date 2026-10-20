#!/usr/bin/env python3
"""Candidate discovery: source reassociation with retuned continuation depths."""
from general_rotations import *
import itertools

def resolver(rows):
    leaves={p:i for i,(p,*_)in enumerate(rows)};depth=max(map(len,leaves))
    def locate(p):
        word=p+'0'*depth
        for k in range(1,depth+1):
            if word[:k]in leaves:return None if'1'in p[k:]else leaves[word[:k]]
        return None
    def inc(p):return ''if not p else format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b')
    def cut(p,b,n):
        pos=[i for i,x in enumerate(p)if x==b]
        return p[:pos[-n]]if len(pos)>=n else''
    def target(p,op,n):
        if op=='CI':return [locate(inc(p))]
        if op=='CD':return [locate(inc(cut(p,'0',1))),locate(inc(p))]
        if op=='CB':return [locate(inc(cut(p,'0',n)))]
        if op=='CC':return [locate(cut(p,'1',n))]
        return []
    return target

def repair(lr,oldgraph):
    rows=c.sites(unlabel(lr));target=resolver(rows);desired={};changes=[]
    for i,(pc,op,n)in enumerate(rows):
        wanted=oldgraph[i][1]
        if target(pc,op,n)==wanted:desired[pc]=(op,n);continue
        if op not in('CB','CC'):return None,dict(reason='fixed_control_changed',site=i)
        choices=[j for j in range(1,5)if target(pc,op,j)==wanted]
        if not choices:return None,dict(reason='no_escape_depth',site=i)
        desired[pc]=(op,choices[0]);changes.append((i,pc,op,n,choices[0]))
    demands=collections.defaultdict(set);changedrows=set()
    def make(n,p=''):
        if ll(n):return desired[p]
        kids=[]
        for b in(0,1):
            ch=make(n[b+1],p+str(b));kids.append(ch)
            if ll(ch):
                demands[n[0],b].add(ch)
                if ch!=n[b+1]:changedrows.add((n[0],b))
        return n[0],*kids
    lrr=make(lr)
    if any(len(demands[r])!=1 for r in changedrows):return None,dict(reason='physical_row_conflict',changes=changes)
    graph,_=c.graph_arithmetic(c.sites(unlabel(lrr)));assert graph==oldgraph
    return lrr,dict(changes=changes,row_commands={r:next(iter(demands[r]))for r in changedrows})

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--basis',type=Path,default=Path(__file__).parent/'full_dn4');a=ap.parse_args()
    t,_=v.parse_table((a.basis/'simplified.tm').read_bytes());lr=labeled(t,c.tree(json.loads((a.basis/'sites225.json').read_text())))
    graph,_=c.graph_arithmetic(c.sites(unlabel(lr)));catalog=collections.defaultdict(collections.Counter)
    def catalog_walk(n):
        if ll(n):return
        for b in(0,1):
            child=n[b+1]
            if ll(child):catalog[child,b][t[n[0],b]]+=1
            else:catalog_walk(child)
    catalog_walk(lr);counts=collections.Counter();out=Path(__file__).parent/'retuned_rotations';out.mkdir(exist_ok=True);records=[]
    for index,rot in enumerate(moves(t,lr,True)):
        tt,ur=perform(t,lr,rot);r,rec=repair(ur,graph)
        if r is None:counts[rec['reason']]+=1;continue
        if not rec['changes']:counts['already_equal']+=1;continue
        counts['source_repairable']+=1;cmds=rec.pop('row_commands');ports=sorted(cmds)
        choices=[list(catalog[cmds[p],p[1]])for p in ports]
        record=dict(rotation=rot,source_changes=rec['changes'],row_commands=[[q,b,*cmds[q,b]]for q,b in ports],row_choice_counts=list(map(len,choices)))
        if any(not z for z in choices):counts['missing_primitive_entry']+=1;records.append(record);continue
        if c.metrics(unlabel(r))['maximum_zero_run']>6:counts['zero7']+=1;records.append(record);continue
        for k,rows in enumerate(itertools.product(*choices)):
            u=tt.copy();u.update(dict(zip(ports,rows)))
            if bad_mapping(u,r):counts['prefix_invalid']+=1;continue
            u,r2,foldrec=probe_folds(u,r);n=len(u)//2;counts['compiled']+=1
            label=f'layout_{index}_{k}'
            if n<=224:label='HIT_'+label
            (out/(label+'.tm')).write_bytes(encode(u));c.dump(out/(label+'_sites.json'),c.sites(unlabel(r2)))
            detail=dict(record,states=n,folds=foldrec,rows=[list(p)+list(row)for p,row in zip(ports,rows)])
            c.dump(out/(label+'_receipt.json'),detail)
            print('COMPILED',label,n,'source_changes',len(rec['changes']),'rows',detail['rows'],'score',foldrec['score'],flush=True)
        records.append(record)
    c.dump(out/'summary.json',dict(counts=dict(counts),records=records));print('DONE',dict(counts),flush=True)
if __name__=='__main__':main()
