from pathlib import Path
import sys,json,hashlib
HERE=Path(__file__).resolve().parent
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--results',type=Path,required=True);args=ap.parse_args()
sys.path.insert(0,str(HERE/'helpers'))
import check_folds as f
import seed_tools as b
out=args.results
old=f.read_table(out/'candidate.k.tm')
folds=[
    dict(keep=118,delete=135,a0=[0,1,155],a1=[1,1,153],invariant={'118':{'0':0},'159':{'1':0}}),
    dict(keep=159,delete=116,a0=[0,1,166],a1=[1,1,118],invariant={})]
receipts=[]
for fold in folds:
    facts,inv=f.check_inductive_invariant(old,fold['invariant'])
    new,phi=f.transformed(old,fold)
    blocks=[]
    for q in (fold['keep'],fold['delete']):
        for bit in (0,1):
            if 0 in facts[q] and facts[q][0]!=bit:continue
            initial=dict(facts[q]);initial[0]=bit
            w,d,z=old[q,bit];expected=dict(initial);expected[0]=w
            block=f.local_block(new,fold['keep'],initial,(phi(z),d,expected),16)
            blocks.append(dict(q=q,bit=bit,**block))
    receipts.append(dict(fold=fold,blocks=blocks,invariant=inv))
    old=new
(out/'candidate222.k.tm').write_bytes(b.table_bytes(old))
(out/'folds.json').write_text(json.dumps(receipts,indent=2)+'\n')
tree=b.s.tree(json.loads((out/'sites.json').read_text()))
g,p=b.decoder_map(old,tree)
print('STATES',len(old)//2,'ALIASES',sum(len(v)-1 for v in g.values()),'ENGINE',len(old)//2-len(g))
print('TABLE_SHA',hashlib.sha256(b.table_bytes(old)).hexdigest())
