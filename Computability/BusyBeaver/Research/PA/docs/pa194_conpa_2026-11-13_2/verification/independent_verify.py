#!/usr/bin/env python3
"""Independent PA194 table, source-graph, and finite-quotient audit.

The compiler, CFG resolver, quotient construction, local simulator, relabeling,
and blank-tape simulator below do not import the candidate builder. The optional
full symbolic pass imports only the pinned, unchanged baseline runtime; its
contracts are generated here from an independently resolved source graph.
This is an executable certificate, not a proof-assistant kernel theorem.
"""
from pathlib import Path
from collections import Counter
import argparse,ast,hashlib,json,re,sys

EXPECTED_DENSE_SHA256='9087d70fc0e1878c38ceff928e6e7e0999c86b6efed00a5ec353821c00641c87'
INC=('leaf','inc',1)
BREAK=('leaf','breakTo',1)
MACROS={'node49':19,'node55':98,'node58':12,'node70':166,'node65':90,
        'node72':69,'node75':213,'node142':194,'node150':221,'node60':99,
        'node61':190,INC:61,(INC,INC):99,((INC,INC),(INC,INC)):190}
PHYSICAL=(6,2,0,4,3,7,8,5,1)
BOX_STATES=(0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198)

def require(condition,message):
    if not condition:raise ValueError(message)

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def read_table(path):
    rows={}
    for line_number,line in enumerate(path.read_text().splitlines(),1):
        if not line or line.startswith('#'):continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        require(b in(0,1)and w in(0,1)and d in('L','R'),'invalid transition')
        require((q,b)not in rows,'duplicate transition')
        rows[q,b]=(w,1 if d=='R'else-1,n)
    states={q for q,b in rows}
    require(set(rows)=={(q,b)for q in states for b in(0,1)},'partial working state')
    return rows

def table_bytes(rows):
    return ''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {n}\n'
                   for(q,b),(w,d,n)in sorted(rows.items())).encode()

def grammar(path):
    data=json.loads(path.read_text());rules=data['rules'];active=set()
    def rec(x):
        if isinstance(x,list):return tuple(x)
        if x not in rules:return x
        require(x not in active,'cyclic grammar');active.add(x)
        parts=rules[x];require(len(parts)==2,'nonbinary grammar')
        result=(rec(parts[0]),rec(parts[1]));active.remove(x);return result
    return rec(data['root'])

def pair(x):return isinstance(x,tuple)and len(x)==2

def compile_raw(t,baseline):
    source=baseline/'vendor/reference'
    match=re.search(r'def labels : List Nat := (\[[^\n]+\])',(source/'PA196/Conjugacy.lean').read_text())
    require(match is not None,'reference labels missing');labels=ast.literal_eval(match[1])
    old=read_table(source/'data/pa196.tm')
    native={(labels[q],b):(w,d,labels[n])for(q,b),(w,d,n)in old.items()}
    rows={k:a for k,a in native.items()if k[0]<1300};allocated={}
    def visit(node):
        if node in MACROS:return MACROS[node]
        if node in allocated:return allocated[node]
        require(pair(node),'unsupported AX node')
        q=2000+len(allocated);allocated[node]=q
        for bit,ch in enumerate(node):
            rows[q,bit]=(0,-1,302)if ch==BREAK else(bit,1,visit(ch))
        return q
    root=visit(t);rows[101,1]=(1,1,root)
    return rows,len(allocated)

def read_source_nodes(path):
    nodes={}
    for line in path.read_text().splitlines():
        m=re.match(r'def (\w+) : Tree := \.node (.*)',line)
        if m is None:continue
        tokens=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2])
        require(len(tokens)==2,'source parse arity')
        nodes[m[1]]=tuple(name if name else('leaf',op,int(arg)if arg else None)for op,arg,name in tokens)
    require('node172'in nodes,'source root missing');return nodes

def flatten_source(t,nodes):
    out=[]
    def walk(x,p):
        if isinstance(x,str):walk(t if x=='x67'else nodes[x],p)
        elif x[0]=='leaf':out.append((p,x[1],x[2]))
        else:
            require(pair(x),'invalid source tree');walk(x[0],p+(0,));walk(x[1],p+(1,))
    walk('node172',());return out

def resolve_source(sites):
    index={p:i for i,(p,op,arg)in enumerate(sites)};spans={}
    require(len(index)==len(sites),'duplicate source address')
    def intervals(p):
        if p in index:result=(index[p],index[p]+1)
        else:
            left,right=intervals(p+(0,)),intervals(p+(1,))
            require(left[1]==right[0],'source interval gap');result=left[0],right[1]
        spans[p]=result;return result
    require(intervals(())==(0,len(sites)),'source interval census')
    def target(path,edge,count):
        while path:
            last=path[-1];path=path[:-1]
            if last==edge:
                count-=1
                if count==0:return spans[path][1]%len(sites)if edge==0 else spans[path][0]
        return 0
    cfg=[]
    for i,(p,op,arg)in enumerate(sites):
        next_i=(i+1)%len(sites)
        if op=='inc':code=('inc',arg,next_i)
        elif op=='dec':code=('dec',arg,target(p,0,1),next_i)
        elif op=='continueTo':code=('jump',target(p,1,arg))
        elif op=='breakTo':code=('jump',target(p,0,arg))
        else:require(op=='halt','source opcode');code=('halt',)
        cfg.append(code)
    return cfg

def macro_word(t):
    if t=='node60':return[INC]*2
    if t=='node61':return[INC]*4
    return macro_word(t[0])+macro_word(t[1])if pair(t)else[t]

def quotient(raw,folds):
    roles=[q for a,b,acts in folds for q in(a,b)]
    require(len(roles)==len(set(roles)),'overlapping folded roles')
    require(74 not in roles and 254 not in roles,'start or halt folded')
    aliases={a:b for a,b,acts in folds}
    replacement={b:[(w,1 if d else-1,n)for w,d,n in acts]for a,b,acts in folds}
    result={}
    for(q,bit),old in raw.items():
        if q in aliases:continue
        w,d,n=replacement[q][bit]if q in replacement else old
        result[q,bit]=w,d,aliases.get(n,n)
    return result,aliases

def local_certificate(raw,folded,folds,aliases):
    history={q:p for a,b,acts in folds for q,p in((a,0),(b,1))};incoming=[]
    for(q,bit),(w,d,n)in raw.items():
        if n in history:
            require(d==1 and w==history[n],'incoming history invariant fails')
            incoming.append([q,bit,w,d,n])
    require({r[4]for r in incoming}==set(history),'unentered fold role')
    for(q,bit),(w,d,n)in raw.items():
        if q not in history:require(folded[q,bit]==(w,d,aliases.get(n,n)),'unaffected row does not commute')
    cases=[]
    for q,left in sorted(history.items()):
        for bit in(0,1):
            w,d,n=raw[q,bit];goal_state=aliases.get(n,n);goal_pos=d
            tape={-1:left,0:bit};wanted={-1:left,0:w};state=aliases.get(q,q);pos=0;steps=[]
            for tick in range(256):
                if tick and(state,pos,tape)==(goal_state,goal_pos,wanted):break
                require(pos in(-1,0),'local detour accessed an outside cell')
                read=tape[pos];require((state,read)in folded,'premature local halt')
                ww,dd,nn=folded[state,read];steps.append([state,pos,read,ww,dd,nn])
                tape[pos]=ww;pos+=dd;state=nn
            else:raise ValueError('local detour did not reach the exact boundary')
            cases.append({'old_state':q,'history_bit':left,'read_bit':bit,'duration':len(steps),
                          'old_transition':[w,d,n],'new_target':goal_state,'steps':steps})
    return {'incoming_rows':incoming,'cases':cases,'case_count':len(cases),
            'duration_histogram':dict(sorted(Counter(r['duration']for r in cases).items())),
            'outside_tape_cells_unread_and_unchanged':True}

def exact_startup(dense,labels,sites):
    state,head,ones=0,0,set()
    for tick in range(58154):
        w,d,state=dense[state,int(head in ones)]
        (ones.add if w else ones.discard)(head);head+=d
    physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    expected={head-1}|{head+i for i,b in enumerate(sites[25][0])if b}
    pos=head+48;expected.add(pos);pos+=1
    for value in physical:
        pos+=1;expected.update(range(pos,pos+value+1));pos+=value+1
    require((labels[state],head)==(84,-2)and ones==expected,'whole blank startup frame differs')
    return {'literal_steps':58154,'native_state':84,'head':head,'seed_ordinal':25,
            'source_path':''.join(map(str,sites[25][0])),'complete_one_positions':sorted(ones),
            'register_values':physical,'outside_tape_all_zero':True}

def run_symbolic(raw,folded,sites,cfg,baseline):
    # The executor is inherited and hash-checked; contract generation is independent.
    sys.path.insert(0,str(baseline/'vendor'));import symbolic_runtime as rt
    contracts=[]
    for i,code in enumerate(cfg):
        start=rt.frame(sites[i][0])
        if code[0]=='inc':
            _,r,n=code;target=rt.canonical(rt.frame(sites[n][0],0,('x','inc',PHYSICAL[r])))
            contracts.append((i,None,start,target))
        elif code[0]=='dec':
            _,r,z,p=code
            contracts.append((i,(PHYSICAL[r],True),start,rt.canonical(rt.frame(sites[z][0]))))
            contracts.append((i,(PHYSICAL[r],False),start,rt.canonical(rt.frame(sites[p][0],1,('x','dec',PHYSICAL[r])))))
        elif code[0]=='jump':contracts.append((i,None,start,rt.canonical(rt.frame(sites[code[1]][0]))))
        else:contracts.append((i,None,start,None))
    results={}
    for name,table in(('unfolded',raw),('folded',folded)):
        boolean_rows={k:(w,d==1,n)for k,(w,d,n)in table.items()}
        result=rt.validate(boolean_rows,contracts);require(result['ok'],name+' symbolic runtime failed');results[name]=result
    return results

def main():
    packet=Path(__file__).resolve().parents[1]
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet',type=Path,default=packet)
    ap.add_argument('--quick',action='store_true',help='Omit only inherited full symbolic-runtime replay')
    args=ap.parse_args();packet=args.packet.resolve();candidate=packet/'pa194';baseline=packet/'reference/pa195_conpa/pa195'
    reference=packet/'reference/separate196/grammar.json'
    if not reference.exists():reference=candidate/'reference/separate196.grammar.json'
    for name,expected in json.loads((baseline/'vendor_hashes.json').read_text()).items():
        require(digest(baseline/name)==expected,'baseline hash mismatch: '+name)
    require(digest(candidate/'pa194.tm')==EXPECTED_DENSE_SHA256,'fixed dense table hash')
    dense=read_table(candidate/'pa194.tm');native=read_table(candidate/'pa194.native.tm');labels=json.loads((candidate/'labels.json').read_text())
    require(len(labels)==195 and len(set(labels))==195 and labels[0]==74 and labels[-1]==254,'dense labeling')
    require(set(dense)=={(q,b)for q in range(194)for b in(0,1)},'dense state/read census')
    require(all(0<=n<=194 for w,d,n in dense.values()),'dense target outside domain')
    require({(labels[q],b):(w,d,labels[n])for(q,b),(w,d,n)in dense.items()}==native,'dense/native conjugacy')
    reached={0};todo=[0]
    for q in todo:
        for bit in(0,1):
            n=dense[q,bit][2]
            if n!=194 and n not in reached:reached.add(n);todo.append(n)
    require(reached==set(range(194)),'advertised state is not graph reachable')
    t=grammar(candidate/'grammar.json');raw,nodes=compile_raw(t,baseline)
    require(nodes==68 and len(raw)==404,'unfolded census')
    require(raw==read_table(candidate/'unfolded202.native.tm'),'independent raw reconstruction')
    require(table_bytes(raw)==(candidate/'unfolded202.native.tm').read_bytes(),'raw canonical bytes')
    folds=json.loads((candidate/'folds.json').read_text());require(len(folds)==8,'fold census')
    rebuilt,aliases=quotient(raw,folds);require(rebuilt==native,'independent quotient reconstruction')
    local=local_certificate(raw,native,folds,aliases);require(local['case_count']==32,'local case census')
    old_native=read_table(baseline/'pa195.native.tm')
    box_keys={(q,b)for q in BOX_STATES for b in(0,1)}
    require(all(raw[k]==native[k]==old_native[k]for k in box_keys),'register-oracle premise row changed')
    nodes_source=read_source_nodes(baseline/'vendor/reference/PA196/Program.lean')
    sites=flatten_source(t,nodes_source);cfg=resolve_source(sites)
    rt=grammar(reference);reference_sites=flatten_source(rt,nodes_source);reference_cfg=resolve_source(reference_sites)
    require(len(sites)==3673,'primitive source census')
    require([s[1:]for s in sites]==[s[1:]for s in reference_sites],'primitive word changed')
    require(cfg==reference_cfg,'source successor graph changed')
    require(macro_word(t)==macro_word(rt)and len(macro_word(t))==190,'macro word changed')
    advertised=json.loads((candidate/'source.json').read_text())
    expected=[{'ordinal':i,'path':''.join(map(str,p)),'op':op,'arg':arg,'instruction':list(cfg[i])}for i,(p,op,arg)in enumerate(sites)]
    require(advertised==expected,'distributed source listing differs')
    startup=exact_startup(dense,labels,sites)
    symbolic=None if args.quick else run_symbolic(raw,native,sites,cfg,baseline)
    receipt={'status':'PASS','dense_sha256':digest(candidate/'pa194.tm'),
             'native_sha256':digest(candidate/'pa194.native.tm'),'unfolded_sha256':digest(candidate/'unfolded202.native.tm'),
             'working_states':194,'binary_rows':388,'start':0,'halt':194,'graph_reachable_working_states':len(reached),
             'independently_allocated_AX_readers':nodes,'unfolded_states':len(raw)//2,'disjoint_folds':len(folds),
             'unchanged_register_oracle_rows':len(box_keys),'incoming_history_rows':len(local['incoming_rows']),'complete_local_cases':local['case_count'],
             'local_duration_histogram':local['duration_histogram'],'outside_cells_arbitrary_and_unchanged':True,
             'source_sites':len(sites),'reference_grammar_sha256':digest(reference),
             'same_ordered_primitive_word':True,'same_independently_resolved_CFG':True,'same_190_token_macro_word':True,
             'maximum_source_path_length':max(len(p)for p,op,arg in sites),
             'startup':startup,'symbolic_runtime_with_independent_contract_generation':symbolic,
             'new_kernel_checked_theorem':False}
    output=packet/'verification';output.mkdir(exist_ok=True)
    (output/'independent_local_certificate.json').write_text(json.dumps(local,indent=2)+'\n')
    (output/('independent_quick_receipt.json'if args.quick else'independent_receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
