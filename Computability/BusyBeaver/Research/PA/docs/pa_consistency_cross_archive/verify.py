#!/usr/bin/env python3
"""Verify the portable packet's positive claims; does not claim a record."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
P=Path(__file__).resolve().parent
if not __debug__:
    raise SystemExit('Use Python with assertions enabled; inherited parsers use assertions.')
sys.path.insert(0,str(P/'research'))
import combine_recent as x

def require(v,msg):
    if not v:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def freeze(v):return tuple(map(freeze,v))if isinstance(v,list)else v
def read_native(path):return x.read_dense(path)
def verify_manifest():
    f=P/'SHA256SUMS'
    require(f.is_file(),'SHA256SUMS missing')
    n=0
    for ln in f.read_text().splitlines():
        h,rel=ln.split('  ',1);path=P/rel
        require(path.is_file()and sha(path)==h,'File digest mismatch: '+rel);n+=1
    return n
def main():
    start=time.monotonic();manifest=verify_manifest()
    original=x.combined.copy();outside=x.outside.copy();records=[]
    specs=[('diagonal_combined',False,3676,4784,57922),('separate_combined',False,3649,4749,57922),('diagonal_combined_zerojump',True,3676,4785,58168),('separate_combined_zerojump',True,3649,4750,58168)]
    for name,zero,nsite,ncase,steps in specs:
        path=P/'machines'/name
        x.combined.clear();x.combined.update(original);x.outside[:]=outside
        if zero:
            x.combined[27,1]=(1,True,21);p,op,arg=x.outside[26];x.outside[26]=(p,'dec',6)
        tree=x.c.read_grammar(path/'grammar.json')
        raw,idx,shape=x.c.build(tree);folds=freeze(json.loads((path/'folds.json').read_text()))
        labels=json.loads((path/'labels.json').read_text())
        require(len(labels)==len(set(labels))==197 and labels[0]==74 and labels[-1]==254,'Bad label map')
        require(len({v for a,b,acts in folds for v in(a,b)})==2*len(folds),'Overlapping source folds')
        folded,aliases=x.s.apply(raw,folds)
        require(folded==read_native(path/'machine.native.tm'),'Regenerated table mismatch '+name)
        dense=x.read_dense(path/'machine.tm')
        require(set(dense)=={(q,b)for q in range(196)for b in(0,1)},'Literal state domain')
        require({(labels[q],b):(w,d,labels[n])for(q,b),(w,d,n)in dense.items()}==folded,'Conjugacy mismatch')
        require(all(folded[q,b]==x.old[q,b]for q in x.c.BOXSTATES for b in(0,1)),'Changed inherited register-engine interface')
        ss,ins,cs=x.c.source(tree)
        require(freeze(ss)==freeze(json.loads((path/'sites.json').read_text())),'Source-site mismatch')
        require(len(ss)==nsite and len(cs)==ncase,'Incorrect source/outcome census')
        rt=x.c.validate(folded,cs);require(rt['ok']and rt['contracts']==ncase,'Symbolic runtime failure')
        st=x.startup(folded,ss);require(st=={'ok':True,'steps':steps},'Exact startup mismatch')
        records.append({'name':name,'states':196,'source_sites':nsite,'cases':ncase,'runtime':rt,'startup':st,'sha256':sha(path/'machine.tm')})
        print(name,': 196 states;',ncase,'uniform cases; startup',steps,flush=True)
    # Bind independently copied review inputs to these exact delivered outputs.
    review=P/'independent_review'
    for i,name in enumerate(('diagonal_combined','separate_combined')):
        for fn in('machine.tm','machine.native.tm','sites.json','grammar.json','labels.json'):
            require((review/'inputs'/f'candidate_{i}_{fn}').read_bytes()==(P/'machines'/name/fn).read_bytes(),'Independent input differs '+name+'/'+fn)
    for i,name in enumerate(('diagonal_combined_zerojump','separate_combined_zerojump')):
        for fn in('machine.tm','machine.native.tm','sites.json','labels.json'):
            require((review/'inputs'/f'zerojump_{i}_{fn}').read_bytes()==(P/'machines'/name/fn).read_bytes(),'Independent zerojump input differs '+name+'/'+fn)
    checks={}
    for f in('verify_grafts.py','check_command_words.py','verify_zerojump_grafts.py','verify_prior_graph_corpus.py'):
        run=subprocess.run([sys.executable,str(review/f)],cwd=review,check=True,capture_output=True,text=True)
        obj=json.loads(run.stdout);checks[f]=obj
        require(obj.get('status')=='PASS','Independent check status '+f)
        print(f,': PASS',flush=True)
    run=subprocess.run([sys.executable,str(P/'comparison/verify_selected.py')],check=True,capture_output=True,text=True)
    checks['selected_tables']=json.loads(run.stdout)
    result={'status':'PASS','requested_sub196_achieved':False,'new_closed_Lean_PA_biconditional':False,'manifest_files':manifest,'machines':records,'independent_checks':checks,'seconds':round(time.monotonic()-start,3),'scope':'Exact table/source/startup checks and inherited unbounded register contracts; written command/calculus proofs are distinguished from a new formal endpoint.'}
    (P/'verification_replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS. The requested sub-196-state construction remains unresolved.',flush=True)
if __name__=='__main__':main()
