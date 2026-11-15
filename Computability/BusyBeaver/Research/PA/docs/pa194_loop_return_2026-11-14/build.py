#!/usr/bin/env python3
"""Rebuild two 194-state machines and check their complete source contracts.
Standard library only. No network, repository checkout or external tape input.
"""
from pathlib import Path
import argparse,hashlib,itertools,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'construction'))
import compiler as c
import support as s

FAMILIES={'PA194LCG':'PA194AX11GH','PA194LCGS':'PA194AX11GHS'}
EXPECTED={'PA194LCG':'5d8e4f5e03c72a8737b898c00a5fbd6e62476cc34a483613ed046d0dc113e84c',
          'PA194LCGS':'ff084fd560d1b2792cda1c443ef522fe4953b1ff0677ad71100fb5e82d19b90b'}
LOOP_PATCH={(139,0):(0,True,99),(139,1):(1,True,190),(190,1):(1,False,73)}
SHORTCUTS={(26,1):(1,True,91),(101,0):(0,True,17),(190,1):(0,False,42)}

def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x

def dump(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def shortcut_certificate(rows):
    """Check every finite premise of the predecessor-invariant proof in report."""
    def pred(q):return [(p,b,w,d)for(p,b),(w,d,n)in sorted(rows.items())if n==q]
    assert s.START not in(11,26,101,190)
    assert pred(101)==[(96,0,0,True)]
    assert pred(26)==[(11,0,0,False),(101,0,0,False)]
    assert pred(11) and all(w==0 for p,b,w,d in pred(11))
    assert pred(190)==[(139,1,1,True)]
    for key,value in { (101,0):(0,False,26),(26,0):(0,True,194),
        (194,0):(0,True,17),(26,1):(1,True,42),(42,0):(0,True,13),
        (13,0):(0,False,91),(190,1):(1,False,73),(73,1):(1,True,83),
        (83,1):(0,False,42)}.items():assert rows[key]==value,(key,rows[key],value)
    fast=dict(rows);fast.update(SHORTCUTS)
    def execute(table,q,tape,steps):
        h=0;tape=dict(tape);trace=[]
        for _ in range(steps):
            assert q!=s.HALT and h in tape
            trace.append([q,h,tape[h]])
            w,d,q=table[q,tape[h]];tape[h]=w;h+=1 if d else -1
        return (q,h,tape),trace
    cases=[]
    for bits in itertools.product((0,1),repeat=5):
        t=dict(zip(range(-2,3),bits))
        for q in(26,101,190):
            guard= (t[0]==1 and t[1]==t[2]==0) if q==26 else (t[-1]==t[0]==0) if q==101 else (t[-1]==t[0]==1)
            if not guard:continue
            old,tr=execute(rows,q,t,3);new,_=execute(fast,q,t,1)
            assert old==new
            cases.append({'state':q,'window':bits,'old_steps':3,'new_steps':1,'final_state':old[0],'head':old[1],'trace':tr})
    assert len(cases)==20
    return {'status':'PASS','predecessors':{str(q):pred(q)for q in(11,26,101,190)},'cases':cases,
      'scope':'Finite hypotheses and identities for the all-tape start-control74 invariant and 3-to-1 clock theorem; see report.'}

def build(name,out,full=True):
    assert __debug__ and not sys.flags.optimize,'Assertions are required.'
    parent=FAMILIES[name];inp=ROOT/'inputs'/parent;out=out/name;out.mkdir(parents=True,exist_ok=True)
    provenance=json.loads((ROOT/'PROVENANCE.json').read_text())['copied_source_hashes']
    for path,digest in provenance.items():
        if path.startswith('inputs/'+parent+'/'):assert sha(ROOT/path)==digest,path
    raw0=s.read_table(inp/'raw.native.tm');old=s.read_table(inp/'machine.native.tm')
    nodes={k:tup(v)for k,v in json.loads((inp/'nodes.json').read_text()).items()}
    grammar=tup(json.loads((inp/'grammar.tree.json').read_text()))
    c.machine=lambda:(raw0,[]);c.raw_nodes=lambda:nodes
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190;c.MACROS['node61']=190
    oldsites,oldins,_=c.source(grammar)
    assert json.loads(json.dumps(oldins))==json.loads((inp/'instructions.json').read_text())
    nodes['node62']=((inc,inc),((inc,inc),('leaf','continueTo',3)))
    c.MACROS.pop(((inc,inc),(inc,inc)));c.MACROS.pop('node61',None)
    fixed=dict(raw0)
    assert fixed[139,0]==(0,True,190)and fixed[139,1]==(0,False,16)and fixed[190,1]==(1,True,99)
    fixed.update(LOOP_PATCH);c.machine=lambda:(fixed,[])
    raw,index,shape=c.build(grammar)
    assert len(raw)==len(raw0) and set(raw)==set(raw0)
    assert set(k for k in raw if raw[k]!=raw0[k])==set(LOOP_PATCH)
    folds=json.loads((inp/'folds.json').read_text());loop,aliases=s.apply_folds(raw,folds)
    local=s.check_local_folds(raw,loop,aliases,folds)
    sites,ins,contracts=c.source(grammar)
    assert ins==oldins
    guards=shortcut_certificate(loop)
    child=dict(loop);child.update(SHORTCUTS)
    assert set(child)==set(old)
    edits=[[q,b,list(old[q,b]),list(child[q,b])]for q,b in sorted(old)if old[q,b]!=child[q,b]]
    assert [e[:2]for e in edits]==[[26,1],[101,0],[139,0],[139,1],[190,1]]
    runtime=c.validate(child,contracts) if full else None
    if full:assert runtime['ok']
    blank=s.startup(child,sites[25][0]);dense,labels=s.dense_table(child,194)
    for fname,table in [('machine.tm',dense),('machine.native.tm',child),('loop_parent.native.tm',loop),('raw_loop.native.tm',raw)]:
        (out/fname).write_text(s.table_text(table))
    assert sha(out/'machine.tm')==EXPECTED[name]
    # Synchronize every shortcut through initialization against the LC parent.
    q=74;h=0;ones=set();old_clock=0;uses={str(q):0 for q in(26,101,190)}
    for _ in range(blank['steps']):
        bit=int(h in ones);k=3 if(q,bit)in SHORTCUTS else 1
        if k==3:uses[str(q)]+=1
        oq,oh,ot=q,h,set(ones)
        for j in range(k):
            w,d,oq=loop[oq,int(oh in ot)];(ot.add if w else ot.discard)(oh);oh+=1 if d else -1
        w,d,q=child[q,bit];(ones.add if w else ones.discard)(h);h+=1 if d else -1
        assert(q,h,ones)==(oq,oh,ot)
        old_clock+=k
    assert (q,h,sorted(ones))==(blank['state'],blank['head'],blank['one_cells'])
    for fname,value in [('nodes.json',nodes),('grammar.tree.json',grammar),('folds.json',folds),('fold_cases.json',local),('shortcut_certificate.json',guards),('instructions.json',ins),('labels.json',labels),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites])]:dump(out/fname,value)
    receipt={'name':name,'parent':parent,'status':'PASS','working_states':194,'transition_rows':388,'start':0,'halt':194,
       'raw_controls':len(raw)//2,'reader_controls':len(shape),'folds':len(folds),'source_sites':len(sites),'source_outcomes':len(contracts),
       'source_graph_equal_to_parent':True,'source_path_changes':sum(a[0]!=b[0]for a,b in zip(oldsites,sites)),
       'native_transition_changes':edits,'local_fold_cases':len(local['cases']),'shortcut_cases':len(guards['cases']),
       'runtime':runtime,'full_construction_replay':full,'startup':blank,'unaccelerated_startup_steps':old_clock,
       'startup_shortcut_uses':uses,'startup_full_prefix_synchronized':True,
       'dense_sha256':sha(out/'machine.tm'),'native_sha256':sha(out/'machine.native.tm'),
       'kernel_checked':False,'proof_scope':'New written relative iPRA theorem. Absolute Con(PA) corollary imports the audited written AX11H calibration and GH/GHS source equivalences.'}
    dump(out/'receipt.json',receipt);print(json.dumps(receipt),flush=True)
    return receipt

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=ROOT/'machines');ap.add_argument('--family',choices=FAMILIES);ap.add_argument('--quick',action='store_true');args=ap.parse_args()
    for name in([args.family]if args.family else FAMILIES):build(name,args.output,not args.quick)
