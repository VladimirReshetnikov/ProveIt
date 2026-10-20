"""Self-authored mathematical TM validation. Reads supplied files as DATA only.
No repository imports, package installation, or downloaded program execution.
Finite regression must not be mistaken for quantified runtime proof.
"""
from pathlib import Path
import json, hashlib, sys, time, os
PACKAGE=Path(__file__).resolve().parent.parent
BASE=Path(os.environ.get('B245_INPUTS',PACKAGE/'inputs'))
OUT=Path(os.environ.get('B245_OUTPUT',PACKAGE/'results'))
PHY=(6,2,0,4,3,7,8,5,1)

def table(p):
    r={}
    for line in Path(p).read_text().splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert (q,b) not in r and b in (0,1) and w in (0,1) and d in ('L','R')
        r[q,b]=(w,1 if d=='R' else -1,t)
    return r

def sites(grammar):
    source=json.loads((BASE/'inputs__closed-sequence-grammar-next22.json').read_text())
    symbols=json.loads((BASE/'inputs__semantic-symbols.json').read_text())
    encoded={v:k for k,v in symbols.items()}
    words={int(q):''.join(encoded[c] for c in word) for q,word in source['flattened_semantic_words'].items()}
    words.update({int(q):word for q,word in grammar.get('root_word_overrides',{}).items()})
    if 'modified_AX_word' in grammar:words[76]=grammar['modified_AX_word']
    rules={w:(a,b) for w,a,b in grammar['rules']}
    overrides={int(i):words[int(q)] for q,i in source['sequence_ast_roots'].items()}
    codes={'inc':'CI','dec':'CD','brk':'CB','cont':'CC','halt':'CH'}
    result=[]
    def ast(i,p):
        if i in overrides and overrides[i] in rules:
            word(overrides[i],p);return
        row=source['ast_dag'][i]
        if row[0]=='L':
            edge=row[1];result.append([p,codes[edge[0]],edge[1] if len(edge)>1 else None])
        else:
            ast(row[1],p+'0');ast(row[2],p+'1')
    def word(w,p):
        if len(w)==1:ast(source['atoms'][symbols[w]]['ast'],p)
        else:
            a,b=rules[w];assert a+b==w
            word(a,p+'0');word(b,p+'1')
    ast(source['original_ast'],'')
    return result

def frame(pc,logical,spares,gap=0):
    values=[None]*9
    for i,j in enumerate(PHY):values[j]=logical[i]
    ones={-1,64+gap}|{i for i,b in enumerate(pc) if b=='1'}
    pos=64+gap+1
    for value in values+list(spares):
        pos+=1;ones.update(range(pos,pos+value+1));pos+=value+1
    return ones

def inc(pc):
    n=len(pc);v=(int(pc,2) if pc else 0)+1
    return (format(v%2**n,'0'+str(n)+'b') if n else ''),int(v==2**n)

def strip(pc,bit,count):
    assert isinstance(count,int) and count>=0
    if count==0:return pc
    for i in range(len(pc)-1,-1,-1):
        if pc[i]==bit:
            count-=1
            if count==0:return pc[:i]
    return ''

def expected(site,regs,spares,gap=0):
    pc,op,r=site;regs=regs.copy();spares=list(spares);delta=0;shift=0
    if op=='CH':return None
    if op=='CI':
        regs[r]+=1;spares.append(1);nxt,shift=inc(pc)
    elif op=='CD' and regs[r]>0:
        regs[r]-=1;delta=1;nxt,shift=inc(pc)
    elif op in ('CD','CB'):
        nxt,shift=inc(strip(pc,'0',r if op=='CB' else 1))
    elif op=='CC':nxt=strip(pc,'1',r)
    else:raise ValueError(site)
    return (96,-shift,{v-shift for v in frame(nxt,regs,spares,gap+delta+shift)}),{'pc':nxt,'registers':regs,'spares':spares,'gap_extra':gap+delta+shift}

def clean_dispatch(q,h,ones):
    if q!=96 or h-1 not in ones or any(x<h-1 for x in ones):return False
    right=sorted(x for x in ones if x>=h+52)
    if not right or right[0]<h+64:return False
    p=right[0]+1;last=max(ones);values=[]
    while p<last:
        if p in ones or p+1 not in ones:return False
        start=p+1;p=start
        while p in ones:p+=1
        values.append(p-start-1)
    return p==last+1 and len(values)>=10

def run(t,pc,regs,spares=(0,),gap=0,limit=100000,trace=False):
    ones=frame(pc,regs,spares,gap);q=96;h=0;used=[]
    for tick in range(limit+1):
        if tick and (clean_dispatch(q,h,ones) or (q,int(h in ones)) not in t):
            return (q,h,ones),tick,used
        if tick==limit:return (q,h,ones),tick,used
        b=int(h in ones);w,d,n=t[q,b]
        if trace:used.append([tick,q,h,b,w,d,n])
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d;q=n

def describe(conf):
    q,h,ones=conf
    return {'state':q,'head':h,'ones':sorted(ones)}

def main():
    grammar=json.loads((BASE/'candidate-routing245/grammar.json').read_text())
    baseline=sites(grammar);assert baseline==json.loads((BASE/'certificate__sites_logical.json').read_text())
    altered=json.loads(json.dumps(grammar));altered['rules']=[([w,'eijkKC','eijkfg'] if w=='eijkKCeijkfg' else [w,a,b]) for w,a,b in altered['rules'] if w!='KCeijkfg']
    changed=sites(altered)
    (OUT/'obvious244-sites.json').write_text(json.dumps(changed,indent=2)+'\n')
    t=table('/workspace/shared/busybeaver245-reduction-20261018/candidate_reassociation244_old.tm')
    old=table(BASE/'candidate-routing245/zfc_routing245_old.tm')
    checked=0;start=time.monotonic()
    for i,s in enumerate(changed):
        for positive in ((False,True) if s[1]=='CD' else (False,)):
            regs=[0]*9
            if positive:regs[s[2]]=1
            want=expected(s,regs,[0]);actual,steps,_=run(t,s[0],regs)
            ok=actual[0]==254 if want is None else actual==want[0]
            if not ok:
                oldwant=expected(baseline[i],regs,[0]);oldactual,oldsteps,_=run(old,baseline[i][0],regs)
                assert oldactual[0]==254 if oldwant is None else oldactual==oldwant[0]
                actual,steps,trace=run(t,s[0],regs,trace=True)
                record={'status':'FALSIFIED','scope':'Concrete valid runtime-frame counterexample, not blank-run claim','site_index':i,'site':s,'baseline_site':baseline[i],'logical_registers':regs,'spares':[0],'header_distance':64,'start_state':96,'start_head':0,'initial_one_cells':sorted(frame(s[0],regs,[0])),'candidate_steps_to_redispatch':steps,'candidate_actual':describe(actual),'expected':describe(want[0]) if want else {'halt':254},'expected_logical':want[1] if want else None,'baseline_same_leaf_passed':True,'baseline_steps':oldsteps,'checked_prior_cases':checked,'trace':trace,'seconds':time.monotonic()-start}
                (OUT/'obvious244-counterexample.json').write_text(json.dumps(record,indent=2)+'\n')
                print(json.dumps({k:v for k,v in record.items() if k not in ('trace','candidate_actual','expected','initial_one_cells')},indent=2));return
            checked+=1
    print('ALL FINITE CASES PASS',checked)

if __name__=='__main__':main()

