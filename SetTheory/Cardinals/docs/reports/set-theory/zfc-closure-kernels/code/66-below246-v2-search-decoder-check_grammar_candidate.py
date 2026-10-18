#!/usr/bin/env python3
"""Reconstruct a semantic grammar candidate and check its actual TM sites."""
from pathlib import Path
from functools import lru_cache
import argparse, hashlib, json, time
import explore as e
import review_affine_source as review

HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('grammar',type=Path);ap.add_argument('symbols',type=Path);ap.add_argument('--name',default='grammar245');args=ap.parse_args()
    data=json.loads((HERE/'closed-sequence-grammar.json').read_text())
    gram=json.loads(args.grammar.read_text());symbols=json.loads(args.symbols.read_text())
    assert all(isinstance(x,str)and ':' in x for x in symbols.values()),'semantic grammar required'
    inverse={v:k for k,v in symbols.items()}
    rules={w:(a,b)for w,a,b in gram['rules']}
    assert len(rules)==gram['rules_count']
    for w,(a,b)in rules.items():
        assert w==a+b
        assert (len(a)==1 or a in rules)and(len(b)==1 or b in rules)
    words={int(q):''.join(inverse[x]for x in word)for q,word in data['flattened_semantic_words'].items()}
    assert set(gram['roots'])=={words[q]for q in data['required_entry_roots']}
    seq=set(data['sequence_states'])
    alloc={words[q]:q for q in seq if words[q]in rules}
    free=iter(sorted(seq-set(alloc.values())))
    for word in sorted(rules):
        if word not in alloc:alloc[word]=next(free)
    assert alloc[words[96]]==96
    def destination(word):
        return int(symbols[word].split(':')[0])if len(word)==1 else alloc[word]
    table={k:v for k,v in e.T.items()if k[0]not in seq}
    for (q,b),(w,d,t)in list(table.items()):
        if t in seq:table[q,b]=(w,d,alloc[words[t]])
    for word,(a,b)in rules.items():
        q=alloc[word];table[q,0]=(0,'R',destination(a));table[q,1]=(1,'R',destination(b))
    assert len(table)==2*(119+len(rules))
    @lru_cache(None)
    def tree(i):
        row=data['ast_dag'][i]
        return ('L',tuple(row[1]))if row[0]=='L'else('N',tree(row[1]),tree(row[2]))
    qtree={tree(i):int(q)for q,i in data['sequence_ast_roots'].items() if words[int(q)] in rules}
    atoms={name:tree(row['ast'])for name,row in data['atoms'].items()}
    @lru_cache(None)
    def changed(t):
        if t in qtree:return expand(words[qtree[t]])
        return t if t[0]=='L'else('N',changed(t[1]),changed(t[2]))
    @lru_cache(None)
    def expand(word):
        if len(word)==1:return changed(atoms[symbols[word]])
        a,b=rules[word];return('N',expand(a),expand(b))
    new=changed(e.ORIGINAL)
    assert len(e.paths(new))==6460
    rows=''.join(f'{q} {b} {w} {d} {t}\n'for(q,b),(w,d,t)in sorted(table.items()))
    tm=HERE/(args.name+'_old.tm');tm.write_text(rows)
    sites=[];logical=[]
    for p,edge in e.paths(new):
        op=edge[0];arg=edge[1]if len(edge)>1 else None
        code=dict(inc='CI',dec='CD',brk='CB',cont='CC',halt='CH')[op]
        logical.append((p,code,arg));sites.append((p,code,e.PHYSICAL[arg]if code in('CI','CD')else arg))
    (HERE/(args.name+'_sites_physical.json')).write_text(json.dumps(sites)+'\n')
    (HERE/(args.name+'_sites_logical.json')).write_text(json.dumps(logical)+'\n')
    (HERE/(args.name+'_allocation.json')).write_text(json.dumps(alloc,indent=2)+'\n')
    started=time.monotonic()
    result=dict(status='PENDING',states=len(table)//2,table=str(tm),table_sha256=hashlib.sha256(tm.read_bytes()).hexdigest(),
        grammar=str(args.grammar),old_max_zero_run=e.maxzeros(e.ORIGINAL),new_max_zero_run=e.maxzeros(new),
        max_leaf_depth=max(len(p)for p,_,_ in sites),source_leaves=len(sites),sequence_rules=len(rules))
    try:
        cert=e.rmpath.certificate(e.ORIGINAL,new);result['rm_bisimulation_entries']=len(cert)
        result['rm_bisimulation']='PASS'
    except Exception as err:
        result['rm_bisimulation']='FAIL';result['rm_error']=repr(err)
    if result['rm_bisimulation']=='PASS':
        affine=review.module(e.BASE/'sources/prior/prefix_affine.py')
        try:
            result['affine']=review.check_sites(affine,{(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in table.items()},sites)
            result['status']='PASS'
        except Exception as err:result['status']='FAIL';result['affine_error']=repr(err)
    else:result['status']='FAIL'
    result['seconds']=time.monotonic()-started
    (HERE/(args.name+'_result.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
