#!/usr/bin/env python3
"""Replay every symbolic source contract using the unmodified Python engine.

The generic arithmetic-block lemmas are inherited and unchanged. These are
universal symbolic frames, not numerical tests of register values. This does
not export an end-to-end iPRA consistency-equivalence proof.
"""
from pathlib import Path
import hashlib,importlib.util,json,sys
P=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('pa194_symbolic_runtime',P/'vendor'/'symbolic_runtime.py')
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
if not __debug__ or sys.flags.optimize:raise RuntimeError('Do not use optimized Python.')
PHYSICAL=[6,4,0,3,2,8,7,5,1]
def require(ok,msg):
    if not ok:raise AssertionError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
    grammar=json.loads((P/'source'/'source_grammar.json').read_text())
    encoded=json.dumps(grammar,separators=(',',':')).encode()
    require(sha(encoded)=='70456686f1a4f3f720be00d2c4a0012f59259b0dc6e2c3c4d675e38dcd089c03','Grammar hash')
    opcodes={'i':'inc','d':'dec','b':'breakTo','c':'continueTo','h':'halt'}
    sites=[]
    def expand(i,p):
        e=grammar['entries'][i]
        if isinstance(e,str):sites.append([p,opcodes[e[0]],int(e[1:]) if len(e)>1 else None])
        else:expand(e[0],p+'0');expand(e[1],p+'1')
    expand(grammar['root'],'')
    require(len(sites)==3673,'Source-site count')
    by_path={p:i for i,(p,_,_) in enumerate(sites)}
    def locate(p):
        if p in by_path:return by_path[p]
        for i,(q,_,_) in enumerate(sites):
            if q.startswith(p) or (p.startswith(q) and '1' not in p[len(q):]):return i
        raise AssertionError(('Missing path',p))
    def after(p):
        for i in range(len(p)-1,-1,-1):
            if p[i]=='0':return locate(p[:i]+'1')
        raise AssertionError(('Source exit',p))
    def cut(p,b,k):
        for i in range(len(p)-1,-1,-1):
            if p[i]==b:
                k-=1
                if not k:return p[:i]
        raise AssertionError(('Missing ancestor',p,b,k))
    def frame(p,extra=0,effect=s.PLAIN):return s.frame(tuple(map(int,p)),extra,effect)
    instructions,contracts=[],[]
    for i,(p,op,arg) in enumerate(sites):
        if op=='inc':ins=['inc',arg,after(p)]
        elif op=='dec':ins=['dec',arg,after(cut(p,'0',1)),after(p)]
        elif op=='breakTo':ins=['jump',after(cut(p,'0',arg))]
        elif op=='continueTo':ins=['jump',locate(cut(p,'1',arg))]
        elif op=='halt':ins=['halt']
        else:raise AssertionError(op)
        instructions.append(ins);initial=frame(p)
        if ins[0]=='inc':contracts.append((i,None,initial,s.canonical(frame(sites[ins[2]][0],0,('x','inc',PHYSICAL[arg])))))
        elif ins[0]=='dec':
            contracts.append((i,(PHYSICAL[arg],True),initial,s.canonical(frame(sites[ins[2]][0]))))
            contracts.append((i,(PHYSICAL[arg],False),initial,s.canonical(frame(sites[ins[3]][0],1,('x','dec',PHYSICAL[arg])))))
        elif ins[0]=='jump':contracts.append((i,None,initial,s.canonical(frame(sites[ins[1]][0]))))
        else:contracts.append((i,None,initial,None))
    instruction_hash=sha((json.dumps(instructions,separators=(',',':'))+'\n').encode())
    require(instruction_hash=='78e7ceb6ada6c162c6a72dea0efc3a0fd9e7c67b2a9015823569f077f3e9d90d','Pinned instruction graph')
    native=(P/'cycle32'/'pa194_cycle32.native.tm').read_bytes()
    require(sha(native)=='7a83339f95624c0d9b3935f081f226b17461dac6c4660e03a400ce04be8e0a9e','Native table hash')
    def table(data):
        rows={}
        for ln in data.decode().splitlines():
            q,b,w,d,n=ln.split();rows[int(q),int(b)]=(int(w),d=='R',int(n))
        return rows
    rows=table(native);base=table((P/'pa194.native.tm').read_bytes())
    require(all(rows[q,b]==base[q,b] for q in s.BOXSTATES for b in (0,1)),'Changed arithmetic block')
    result=s.validate(rows,contracts)
    require(result=={'ok':True,'contracts':4780,'max_steps':497,'total_steps':1479348},'Source contract receipt')
    receipt={'name':'PA194C32','status':'PASS','source_sites':len(sites),'native_sha256':sha(native),'source_instructions_sha256':instruction_hash,'symbolic':result,'arithmetic_box_oracles':True,'arithmetic_box_rows_unchanged':True,'proof_assistant_kernel_checked':False,'arithmetical_calibration_proved':False,'scope':'Universal source-frame contracts using the unchanged imported arithmetic-block lemmas.'}
    (P/'receipts'/'python_source.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
