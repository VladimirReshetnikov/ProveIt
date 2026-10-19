#!/usr/bin/env python3
"""Exact-table unary/list induction certificate for the K230 source and derivatives.

The driver uses canonical K230 labels including holes after deletion; a separate
bijection certifies final contiguous numbering. No finite fixture is used as a
universal proof. Bounds below limit proof search only.
"""
from pathlib import Path
import argparse,json,hashlib,sys,time
import symbolic_runtime_k as s

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(x,msg):
    if not x:raise ValueError(msg)
def parse(p):
    t={};start=[]
    for line in Path(p).read_text().splitlines():
        if line.startswith('#! start '):start.append(int(line[9:]))
        elif line and not line.startswith('#'):
            q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
            require((q,b) not in t and b in (0,1) and w in(0,1) and d in('L','R'),'Malformed row')
            t[q,b]=(w,1 if d=='R' else -1,z)
    qs={q for q,b in t};require(start==[0],'Wrong initial state')
    require(set(t)=={(q,b) for q in qs for b in(0,1)},'Partial table')
    require({z for w,d,z in t.values()}-qs=={230},'Wrong halt label')
    return t
def sites_check(ss):
    words=set();prefixes=set()
    for p,o,r in ss:
        require(isinstance(p,str) and 0<len(p)<64 and set(p)<={'0','1'},'Malformed PC')
        require(p not in words,'Duplicate PC');words.add(p);prefixes.update(p[:i] for i in range(len(p)))
        require(o in('CI','CD','CB','CC','CH'),'Opcode')
        require((o=='CH' and r is None) or (o!='CH' and type(r) is int and r>=0),'Operand')
        require(o not in ('CI','CD') or r<9,'Register outside primary9')
    require(not words&prefixes and len(prefixes)==len(words)-1,'Not a full prefix code')
    require(all(p+b in words or p+b in prefixes for p in prefixes for b in'01'),'Incomplete source tree')
    return sum(2 if o=='CD' else 1 for p,o,r in ss)
def main():
    require(__debug__ and not sys.flags.optimize,'Enable Python assertions')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--table',type=Path,required=True);ap.add_argument('--source',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True);ap.add_argument('--limit',type=int,default=0);a=ap.parse_args()
    t=parse(a.table);ss=json.loads(a.source.read_text());expected=sites_check(ss);a.output.parent.mkdir(parents=True,exist_ok=True)
    receipt=dict(status='IN_PROGRESS',table_sha256=sha(a.table),source_sha256=sha(a.source),states=len(t)//2,rows=len(t),expected_cases=expected,
                 checker_sha256=sha(__file__),engine_sha256=sha(s.__file__),helper_sha256=sha(s.r.__file__),
                 scope='All independent natural primary register values, both decrement guards, arbitrary nonnegative extra gap, arbitrary first spare and arbitrary finite spare tail; exact entire tape and positive duration. Ordinary mathematical proof, no new Rocq endpoint claimed.',
                 proof_budget_per_case=4000,budget_scope='Proof construction only, no bound on concrete machine duration or input values.')
    begin=time.monotonic();cases=[];used=set()
    def save():
        receipt.update(cases=len(cases),seconds=time.monotonic()-begin);a.output.write_text(json.dumps(receipt,indent=2)+'\n')
    try:
        lemmas,blocks=s.prove_blocks(t);receipt['list_induction_blocks']=blocks;print('Four exact-table list schemas PASS',flush=True)
        for i,site in enumerate(ss):
            for positive in ((False,True) if site[1]=='CD' else (False,)):
                result=s.case(t,lemmas,site,positive);used.update(result.pop('rows'));result.pop('trace')
                cases.append(dict(site_index=i,positive=positive,**result))
                if len(cases)%1000==0:save();print('proved',len(cases),'cases in',round(time.monotonic()-begin,3),'s',flush=True)
                if a.limit and len(cases)>=a.limit and len(cases)<expected:
                    receipt['status']='PARTIAL_PREFIX_PASS';save();return
        require(len(cases)==expected,'Incomplete source case set')
        file=a.output.with_name(a.output.stem+'_cases.json');file.write_text(json.dumps(cases,indent=2)+'\n')
        receipt.update(status='UNIVERSAL_MATHEMATICAL_PASS',symbolic_steps=sum(c['symbolic_steps'] for c in cases),maximum_symbolic_steps=max(c['symbolic_steps'] for c in cases),minimum_actual_steps=min(c['duration'][0] for c in cases),used_rows=sorted(used),unused_rows=sorted(set(t)-used),cases_file=file.name,cases_sha256=sha(file))
        save();print(json.dumps({k:x for k,x in receipt.items() if k not in('list_induction_blocks','used_rows')},indent=2),flush=True)
    except Exception as exc:
        receipt.update(status='NOT_PROVED',site_index=locals().get('i'),site=locals().get('site'),positive=locals().get('positive'),error=repr(exc));save();raise
if __name__=='__main__':main()
