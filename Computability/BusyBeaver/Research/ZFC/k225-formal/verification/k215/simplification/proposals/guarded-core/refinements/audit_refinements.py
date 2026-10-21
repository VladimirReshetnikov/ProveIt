#!/usr/bin/env python3
"""Owned read-only packet audit and independent finite checks. Never imports packet code.

No Lean, Coq, or Rocq proof is run. Output is corroboration, not kernel evidence.
"""
from pathlib import Path
from collections import Counter
import hashlib, itertools, json, math, os, re, sys

if sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('OPTIMIZED_MODE_REJECTED: run without -O, -OO, or PYTHONOPTIMIZE.')

ROOT = Path(__file__).resolve().parent
P = ROOT / 'incoming/K215_Certificate_Refinements_2026-10-21'
def require(b, label):
    if not b: raise ValueError(label)
def sha(b): return hashlib.sha256(b).hexdigest()
def data(p): return json.loads(p.read_text())

def audit():
    man = data(P/'manifest.json')['files']
    actual = {p.relative_to(P).as_posix() for p in P.rglob('*') if p.is_file()}
    require(set(man)|{'manifest.json'} == actual, 'manifest coverage')
    for path, m in man.items():
        b=(P/path).read_bytes()
        require(len(b)==m['bytes'] and sha(b)==m['sha256'], 'manifest '+path)
    B=P/'balanced_lookup'; receipt=data(B/'evidence/result.json')
    result=[]
    for r in receipt['results']:
        path=r['file']; src=B/path
        if path=='deps/K230/RMEquiv.v':
            b=(B/'deps/K230/RMEquiv.rocq91.v').read_bytes()
            key=b'From K230 Require Import RM.'
            require(b.count(key)==1,'compat substitution unique')
            b=b.replace(key,key+b'\nRequire Import Compat818.')
        else: b=src.read_bytes()
        require(sha(b)==r['source_sha256'], 'receipt source '+path)
        log=(B/'evidence'/str(path.replace('/','_')+'.log')).read_bytes()
        require(sha(log)==r['log_sha256'], 'receipt log '+path)
        require(log.count(b'Closed under the global context')==r['closed_reports'], 'closed reports')
        require(r['exit_code']==0 and b'Axioms:' not in log,'compiler status')
        result.append(path)
    generic=receipt['recursive_generic_check']
    require(generic['exit_code']==0,'generic recursive exit')
    require(sha((B/'evidence/coqchk_BalancedBisim.log').read_bytes())==generic['log_sha256'],'generic recursive log')
    mr=data(P/'marker_certificate/verification-final/receipt.json')
    for path,h in mr['sources'].items():
        require(sha((P/'marker_certificate'/path).read_bytes())==h,'marker source '+path)
    require(all(x['returncode']==0 for x in mr['commands']),'marker exits')
    ml=b''.join(x.read_bytes() for x in (P/'marker_certificate/verification-final').glob('*.log'))
    require(ml.count(b'Closed under the global context')==mr['closed_assumption_reports']==6,'marker reports')
    zr=data(P/'zero_credit/verification-final/receipt.json')
    require(sha((P/'zero_credit/CantorCredit.v').read_bytes())==zr['source_sha256'],'credit source')
    require(all(x['exit_code']==0 for x in zr['steps']),'credit exits')
    zl=(P/'zero_credit/verification-final/coqc.log').read_bytes()
    require(zl.count(b'Closed under the global context')==zr['closed_assumption_reports']==9,'credit reports')
    holes=[]
    for f in P.rglob('*.v'):
        # Strip nested Coq comments before searching for admitted/custom axioms.
        text=f.read_text(); out=[]; depth=0; i=0
        while i<len(text):
            if text[i:i+2]=='(*': depth+=1; i+=2
            elif depth and text[i:i+2]=='*)': depth-=1; i+=2
            else:
                if not depth: out.append(text[i])
                i+=1
        require(depth==0,'closed comments')
        if re.search(r'\b(?:Admitted|admit|Axiom|Axioms|Parameter|Parameters)\b',''.join(out)):
            holes.append(f.relative_to(P).as_posix())
    return {'manifest_files_verified':len(man),'balanced_source_and_log_bindings':len(result),
            'balanced_recursive_target':generic['target'],'marker_closed_reports':6,'credit_closed_reports':9,
            'custom_axiom_or_admit_tokens':holes,
            'proof_assistant_replay':'Not attempted; tool availability is not a portable audit result.',
            'proof_execution_in_this_review':False,'incoming_executable_execution':False,
            'object_hashes_not_recomputed':'Compiled objects are intentionally absent.'}

def unpack(n):
    require(n>0,'positive path'); out=[]
    while n!=1: out.append(bool(n&1)); n//=2
    return tuple(out)
def pack(p):
    n=1
    for b in reversed(p): n=2*n+int(b)
    return n
def inc(p):
    p=list(p)
    for i in range(len(p)-1,-1,-1):
        p[i]=not p[i]
        if p[i]: break
    return tuple(p)
def strip(bit,k,p):
    p=list(p)
    while p and k: k-=p.pop()==bit
    return tuple(p)
def brk(k,p): return inc(strip(False,k,p))
def edge(s):
    k,*a=s.split(); return ({'CN':'N','CI':'I','CD':'D','CB':'B','CC':'C','CH':'H','ENode':'N','EInc':'I','EDecnz':'D','EBreak':'B','EContinue':'C','EHalt':'H'}[k], int(a[0]) if a else None)
def programs():
    B=P/'balanced_lookup/deps/K215F'
    text=(B/'Prog215.v').read_text().split('Definition p215_tab',1)[1].split('].',1)[0]
    a=[(edge(x),edge(y)) for x,y in re.findall(r'\((C\w+(?: \d+)?), (C\w+(?: \d+)?)\)',text)]
    require(len(a)==179,'p215 parsed')
    rows=re.findall(r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)',(B/'DagPerm.v').read_text())
    require([int(i) for i,_,_ in rows]==list(range(487)),'dag parsed')
    b=[(edge(x),edge(y)) for _,x,y in rows]
    return (a,178),(b,0)
def site(prog,p):
    nodes,q=prog
    for i in range(len(nodes)+1):
        e=nodes[q][p[i] if i<len(p) else False]
        if e[0]!='N': return e,(p+(False,)*(i+1))[:i+1]
        q=e[1]
    raise ValueError('site fuel')
def segment(prog,p):
    c=Counter()
    for i in range(1000):
        (op,r),q=site(prog,p)
        if op in ('D','H'): return c,p
        if op=='I': c[r]+=1; p=inc(q)
        elif op=='B': p=brk(r,q)
        elif op=='C': p=strip(True,r,q)
        else: raise ValueError('unexpected node')
    raise ValueError('segment fuel')

def source_and_radix():
    t=(P/'balanced_lookup/Cert215Compact.v').read_text()
    cert=[tuple(map(int,r)) for r in re.findall(r'\((\d+)%positive,(\d+)%positive,(\d+)%N,(\d+)%N\)',t)]
    require(len(cert)==2240,'certificate count')
    paths={}
    def build(lo,hi,path=()):
        if hi-lo==1: paths[lo]=path; return ('leaf',lo)
        cut=(hi-lo)//2
        return ('node',build(lo,lo+cut,path+(False,)),build(lo+cut,hi,path+(True,)))
    tree=build(0,len(cert)); codes={i:pack(p) for i,p in paths.items()}
    def lookup(code):
        node=tree; visits=1
        while node[0]=='node':
            if code==1:return None,visits
            node=node[2 if code&1 else 1]; code//=2; visits+=1
        return (node[1] if code==1 else None),visits
    remapped=[(a,b,codes[j],codes[k]) for a,b,j,k in cert]
    def build_payload(prefix=0,depth=0):
        key=(1<<depth)+prefix
        if key>len(cert): return None
        return (key-1,build_payload(prefix,depth+1),build_payload(prefix+(1<<depth),depth+1))
    payload_tree=build_payload()
    def lookup_payload(code):
        node=payload_tree; visits=0
        while node is not None:
            visits+=1
            if code==1:return node[0],visits
            node=node[2 if code&1 else 1]; code//=2
        return None,visits
    p1,p2=programs(); visits=[]; payload_visits=[]; old_queries=[]; halted=[]
    def branch(a,b,j,newj):
        c1,q1=segment(p1,a); c2,q2=segment(p2,b)
        idx,d=lookup(newj)
        require(idx==j,'radix target identity')
        x,y,_,_=cert[idx]
        require(c1==c2 and q1==unpack(x) and q2==unpack(y),'full branch check')
        old_queries.append(j); visits.append(d)
        idx2,d2=lookup_payload(j+1)
        require(idx2==j,'payload trie target identity')
        payload_visits.append(d2)
    branch((),(),0,codes[0])
    for i,((a,b,j,k),(_,_,newj,newk)) in enumerate(zip(cert,remapped)):
        a,b=unpack(a),unpack(b)
        (op,r),q=site(p1,a); (op2,r2),q2=site(p2,b)
        if op==op2=='H':halted.append(i); continue
        require(op==op2=='D' and r==r2,'matching decrement checkpoint')
        branch(inc(q),inc(q2),j,newj); branch(brk(1,q),brk(1,q2),k,newk)
    # Every possible positive code through the maximum depth: reject wrong shapes,
    # return exactly one included leaf otherwise. This tests containment, not semantics.
    count=0
    for j in range(1,1<<14):
        idx,_=lookup(j)
        if idx is not None: require(codes[idx]==j,'leaf address'); count+=1
        idx2,_=lookup_payload(j)
        require(idx2==(j-1 if j<=2240 else None),'payload trie all valid/out-of-range keys')
    require(count==2240,'all and only leaves addressable')
    result={'entries':2240,'halt_entry_indices':halted,'full_semantic_branch_checks':len(visits),
      'ordinal_list_node_visits':sum(j+1 for j in old_queries),'ordinal_balanced_and_radix_node_visits':sum(visits),
      'max_lookup_visits':max(visits),'radix_internal_nodes':2239,'stored_cut_fields_removed':2239,
      'initial_reference':codes[0],'max_used_radix_reference':max(codes.values()),
      'max_radix_reference_bits':max(codes.values()).bit_length(),
      'old_successor_bits_total':sum(j.bit_length()+k.bit_length() for _,_,j,k in cert),
      'radix_successor_bits_total':sum(j.bit_length()+k.bit_length() for _,_,j,k in remapped),
      'radix_root_and_successor_constructor_steps':sum(visits)-len(visits),
      'exhaustive_positive_code_checks':(1<<14)-1,
      'status':'FINITE_REINDEXING_AND_SOURCE_CHECK_PASSED_NOT_COMPILED'}
    artifact={'format':'ordered full binary tree, midpoint split; positive LSB-first leaf addresses; no size fields',
              'entry_count':2240,'initial':codes[0],'entries':remapped,
              'warning':'Uncompiled research data. No production checker accepts this format yet.'}
    (ROOT/'radix_certificate.json').write_text(json.dumps(artifact,separators=(',',':'))+'\n')
    result['artifact_sha256']=sha((ROOT/'radix_certificate.json').read_bytes())
    def serialize(node):
        if node is None:return None
        i,left,right=node; a,b,j,k=cert[i]
        return {'e':[a,b,j+1,k+1],'l':serialize(left),'r':serialize(right)}
    preferred={'format':'positive binary trie; each nonempty node holds one checkpoint; xH returns current, xO left, xI right',
               'initial':1,'entry_count':2240,'tree':serialize(payload_tree),
               'warning':'Uncompiled research data. Production checker needs generic lookup-coverage soundness.'}
    (ROOT/'positive_trie_certificate.json').write_text(json.dumps(preferred,separators=(',',':'))+'\n')
    def cut_bits(n):
        if n<2:return 0
        k=n//2; return k.bit_length()+cut_bits(k)+cut_bits(n-k)
    result['preferred_payload_trie']={
        'payload_nodes':2240,'empty_child_slots':2241,'initial_reference':1,
        'reference_relabeling':'old ordinal j becomes positive j+1',
        'max_lookup_visits':max(payload_visits),'lookup_node_visits':sum(payload_visits),
        'lookup_digit_descents':sum(payload_visits)-len(payload_visits),
        'node_visits_saved_vs_balanced':sum(visits)-sum(payload_visits),
        'percent_fewer_node_visits_vs_balanced':100*(1-sum(payload_visits)/sum(visits)),
        'old_successor_binary_digits':result['old_successor_bits_total'],
        'new_successor_binary_digits':sum((j+1).bit_length()+(k+1).bit_length() for _,_,j,k in cert),
        'removed_cut_binary_digits':cut_bits(2240),'removed_cut_fields':2239,
        'binary_digit_counts_exclude_structural_constructors':True,
        'artifact_sha256':sha((ROOT/'positive_trie_certificate.json').read_bytes()),
        'full_semantic_branch_checks':len(payload_visits),'exhaustive_code_checks':(1<<14)-1,
        'status':'PREFERRED_FINITE_PROTOTYPE_NOT_COMPILED'}
    return result

def machine(path):
    rows={}
    for line in path.read_text().splitlines():
        if line.startswith('#') or not line.strip():continue
        q,b,w,d,z=line.split(); key=int(q),int(b)
        require(key not in rows,'duplicate row'); rows[key]=(int(w),1 if d=='R' else -1,int(z))
    return rows
def marker():
    M=P/'marker_certificate'; tables={n:machine(M/(n+'.tm')) for n in ['K215','M124','FM215','M125']}
    source=(M/'MarkerTables.v').read_text()
    def parse_opt(s):
        if s=='None':return None
        m=re.fullmatch(r'Some \(I (true|false) (true|false) (\d+)\)',s)
        require(m is not None,'literal Coq instruction')
        return int(m[1]=='true'),1 if m[2]=='true' else -1,int(m[3])
    result={}
    for n,T in tables.items():
        body=source.split('Definition '+n+' : table := [',1)[1].split('].',1)[0]
        rows=re.findall(r'^  \((None|Some \(I (?:true|false) (?:true|false) \d+\)), (None|Some \(I (?:true|false) (?:true|false) \d+\))\)[;\s]*$',body,re.M)
        require(len(rows)==303,'303 literal slots')
        parsed={(q,b):parse_opt(row[b]) for q,row in enumerate(rows) for b in [0,1] if parse_opt(row[b]) is not None}
        require(T==parsed,'exact tm/Coq rows '+n)
        states={q for q,_ in T}; require(len(states)==215 and len(T)==430,'215 complete states')
        require(all((q,b) in T for q in states for b in [0,1]),'complete rows')
        require(all(z in states or z==254 for _,_,z in T.values()),'transition closure')
        result[n]={'working_states':215,'rows':430,'literal_Coq_rows_identical':True}
    O=tables['K215']; phi=lambda q:124 if q==127 else q
    for n,provider in [('M124',59),('FM215',109),('M125',125)]:
        T=tables[n]
        for (q,b),(w,d,z) in O.items():
            require(z!=124 or (w,d)==(1,1),'incoming a')
            require(z!=127 or (w,d)==(0,1),'incoming b')
            if q not in [124,127]:require(T[(phi(q),b)]==(w,d,phi(z)),'outer')
        shapes={(124,0):(0,-1,127),(124,1):(1,1,138),(127,0):(0,1,8),
                (127,1):(1,1,provider),(8,0):(0,1,14),(provider,0):(0,1,62)}
        require(all(T[k]==v for k,v in shapes.items()),'new shapes')
        require(all(O[k]==v for k,v in {(124,0):(0,1,62),(127,0):(0,1,14),(124,1):(1,1,138),(127,1):(1,1,138)}.items()),'old shapes')
        require((254,0) not in T and (254,1) not in T,'halt stable')
        cases=0
        # Five relevant cells plus two distant one-cells are a finite frame control.
        for bits in itertools.product([0,1],repeat=5):
            tape={i-2 for i,b in enumerate(bits) if b}|{-100,100}
            for q in [124,127]:
                if ((-1 in tape)!=(q==124)):continue
                def step(S,c):
                    state,h,cells=c; row=S.get((state,int(h in cells)))
                    if row is None:return c
                    w,d,z=row; new=set(cells)
                    if w:new.add(h)
                    else:new.discard(h)
                    return z,h+d,new
                old=step(O,(q,0,tape)); new=(124,0,tape)
                for _ in range(1 if 0 in tape else 3):new=step(T,new)
                require(new==(phi(old[0]),old[1],old[2]),'whole finite tape local block')
                cases+=1
        old=(0,0,set()); new=(0,0,set()); clock=blocks=0
        for _ in range(95714):
            d=3 if old[0] in [124,127] and old[1] not in old[2] else 1
            blocks+=d==3; old=step(O,old)
            for _ in range(d):new=step(T,new)
            clock+=d; require(new==(phi(old[0]),old[1],old[2]),'startup full synchronization')
        require((new[0],new[1],len(new[2]),clock,blocks)==(84,-8,95,95840,63),'startup endpoints')
        result[n].update(local_frame_cases=cases,startup_old_steps=95714,startup_new_steps=clock,three_step_blocks=blocks)
    rename=data(M/'M125.canonicalization.json'); mp={int(k):v for k,v in rename['native_to_dense'].items()}
    dense=machine(M/'M125.dense.tm')
    require(len(set(mp.values()))==216 and set(mp.values())==set(range(216)),'bijective dense map')
    require({(mp[q],b):(w,d,mp[z]) for (q,b),(w,d,z) in tables['M125'].items()}==dense,'exact dense relabel')
    return result

def credit():
    # Independent concrete arithmetic, not the incoming executable decoder.
    def pair(x,y):return (x+y)*(x+y+1)//2+y
    def split(n):
        s=(math.isqrt(8*n+1)-1)//2; y=n-s*(s+1)//2
        return s-y,y
    def decode(n):
        word=[]
        while True:
            tag,r=split(n)
            if tag==0:k=('DROP',)
            elif tag==1:k=('NIP',)
            elif tag==2:
                x,r=split(r); k=('MP',x)
            else:
                y,r=split(r); x,r=split(r); k=('AX',tag-3,x,y)
            word.append(k)
            if r==0:return tuple(word)
            require(r-1<n,'concrete residual descent'); n=r-1
    def emit(k,r):
        if k[0]=='DROP':return pair(0,r)
        if k[0]=='NIP':return pair(1,r)
        if k[0]=='MP':return pair(2,pair(k[1],r))
        return pair(k[1]+3,pair(k[3],pair(k[2],r)))
    def encode(word):
        out=emit(word[-1],0)
        for k in reversed(word[:-1]):out=emit(k,out+1)
        return out
    balance=0; pop_count=push_count=occurrences=0; images=set()
    for n in range(10000):
        w=decode(n); require(encode(w)==n,'concrete codec roundtrip')
        for j,k in enumerate(w):
            occurrences+=1
            if k==('DROP',):balance+=1;push_count+=1
            if k==('NIP',):
                require(balance>0,'strict protected credit before NIP')
                lower=w[:j]+(('DROP',),)+w[j+1:]; lowered=encode(lower)
                require(lowered<n,'lowered candidate earlier')
                require(decode(lowered)==lower,'lowered word roundtrip')
                key=(lowered,j); require(key not in images,'occurrence injection'); images.add(key)
                balance-=1;pop_count+=1
            require(balance>=0,'every command prefix nonnegative')
    return {'complete_candidates':10000,'command_occurrences':occurrences,'DROP_count':push_count,
            'NIP_count':pop_count,'final_credit':balance,'distinct_lowered_NIP_occurrences':len(images),
            'scope':'Finite corroboration of concrete codec, lowering, and each syntactic prefix; no physical machine connection.'}

def main():
    result={'scope':'Owned Python evidence only; incoming executables never run; no proof-assistant replay.',
            'receipt_audit':audit(),'radix_refinement':source_and_radix(),'marker_data':marker(),'credit_finite':credit()}
    (ROOT/'AUDIT_RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
