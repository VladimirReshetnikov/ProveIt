#!/usr/bin/env python3
"""Finite binding checks for the written PA194OM/PA194OMF relative proof.

Usage: check_relative_om.py --parent PATH --om PATH --omf PATH --out FILE
The supplied machine directories contain tables, labels, sites, instructions,
and independently produced contracts.  This is a small independent inspector,
not a replacement for the uniform literal source-contract replay.
"""
from pathlib import Path
import argparse, hashlib, itertools, json

def require(p,msg):
    if not p:raise AssertionError(msg)

def read_table(path):
    result={}
    for line in path.read_text().splitlines():
        if not line.strip():continue
        q,b,w,d,n=line.split();key=(int(q),int(b))
        require(key not in result,'duplicate table row')
        result[key]=(int(w),1 if d=='R' else -1,int(n))
    return result

def step(table,c):
    q,h,ones=c
    if q==254:return c
    w,d,n=table[q,int(h in ones)];ones=set(ones)
    if w:ones.add(h)
    else:ones.discard(h)
    return n,h+d,ones

def run(table,c,t):
    for _ in range(t):c=step(table,c)
    return c

def expected_seed(path):
    r=[int(x)for x in path]+[0]*(48-len(path))+[1]
    for v in [0,0,0,0,0,0,2,0,0]+[1]*26:r += [0]+[1]*(v+1)
    return 84,-2,{-3}|{i-2 for i,b in enumerate(r)if b}

def prefix_reader(table,start,code):
    q=start
    for bit in map(int,code):
        w,d,q=table[q,bit];require((w,d)==(bit,1),'reader preserves bit and moves right')
    return q

def source_successor_closure(sites,instructions):
    """Bind arithmetic header updates to every canonical source successor.

    This repeats neither the constructor's resolver nor a physical trace.
    Equal 48-bit padded words remain equal after any common additional
    zero padding, including the extra cell from a positive decrement.
    """
    def padded(word):
        require(len(word)<=48 and all(b in '01'for b in word),'binary header word')
        return word+'0'*(48-len(word))
    lookup={padded(row[0]):i for i,row in enumerate(sites)}
    require(len(lookup)==len(sites),'distinct padded source addresses')
    checks=0
    def target(word,increment=False):
        nonlocal checks
        if increment:
            value=(int(word,2)if word else 0)+1
            require(value<2**len(word),'zero address overflow')
            word=format(value,'0'+str(len(word))+'b')
        code=padded(word)
        require(code in lookup,'arithmetic successor has a canonical padded address')
        checks+=1
        return lookup[code]
    def cut(word,bit,count):
        require(isinstance(count,int)and count>=0,'natural relative branch count')
        if count==0:return word
        places=[i for i,b in enumerate(word)if b==bit]
        return word[:places[-count]]if len(places)>=count else ''
    for (word,op,arg),actual in zip(sites,instructions):
        if op=='inc':expected=['inc',arg,target(word,True)]
        elif op=='dec':expected=['dec',arg,target(cut(word,'0',1),True),target(word,True)]
        elif op=='breakTo':expected=['jump',target(cut(word,'0',arg),True)]
        elif op=='continueTo':expected=['jump',target(cut(word,'1',arg))]
        else:
            require(op=='halt','known source operation');expected=['halt']
        require(actual==expected,'source operation and every resolved successor agree')
    require(checks==4777,'all nonhalting source outcomes bound to canonical successors')
    return dict(nonhalting_outcomes=checks,zero_overflow=True,
                canonical_padded_successors=True,base_header_width=48)

def inspect(path,name,startup):
    native=read_table(path/'machine.native.tm');dense=read_table(path/'machine.tm')
    labels=json.loads((path/'labels.json').read_text())
    sites=json.loads((path/'sites.json').read_text())
    ins=json.loads((path/'instructions.json').read_text())
    contracts=json.loads((path/'independent/contracts.json').read_text())
    require(len(labels)==195 and labels[0]==74 and labels[-1]==254,'labels and endpoints')
    require(len(set(labels))==195,'injective label map')
    require(set(native)==set(itertools.product(labels[:-1],[0,1])),'complete native table')
    require(set(dense)==set(itertools.product(range(194),[0,1])),'complete dense table')
    for (q,b),(w,d,n) in dense.items():
        require(native[labels[q],b]==(w,d,labels[n]),'literal dense/native conjugacy')
    require(len(sites)==len(ins)==3671,'source size')
    require(sites[25][0]=='1000000' and max(len(x[0])for x in sites)<=48,'address header fit')
    successor_closure=source_successor_closure(sites,ins)
    expected=[(i,p)for i,row in enumerate(ins)for p in ([False,True]if row[0]=='dec'else[False])]
    require([(x['site'],x['positive'])for x in contracts]==expected,'complete ordered outcome index')
    require(len(contracts)==4778,'outcome count')
    for x in contracts:
        require(len(x['duration'])==13 and all(isinstance(v,int)and v>=0 for v in x['duration']),'nonnegative affine duration')
        require(x['duration'][0]>=3,'positive live duration')
        if ins[x['site']][0]!='halt':require(x['motion']==[0]*13,'zero complete-frame displacement')
        else:require(x['duration']==[3]+[0]*12,'exact halt duration')
    maxima=[max(x['duration'][i]for x in contracts)for i in range(13)]
    bound=[534,8,4,4,4,4,4,4,2,4,4,2,2]
    require(all(x<=y for x,y in zip(maxima,bound)),'common affine bound')
    c=(74,0,set());visited=set()
    for _ in range(startup):
        require(c[0]!=254,'startup did not halt')
        visited.add((c[0],int(c[1]in c[2])));c=step(native,c)
    require(c==expected_seed(sites[25][0]),'entire blank startup tape, head and state')
    return dict(name=name,states=194,source_sites=len(ins),source_outcomes=len(contracts),
        successor_closure=successor_closure,
        max_address_length=max(len(x[0])for x in sites),affine_maxima=maxima,
        minimum_constant=min(x['duration'][0]for x in contracts),startup=startup,
        entire_startup=True,sha256=hashlib.sha256((path/'machine.tm').read_bytes()).hexdigest(),
        per_site_bound=[694,18],clock=[startup,685,9]),native,ins,sites,visited

def sf_cases(old,new):
    expected={(26,1):(1,1,91),(101,0):(0,1,17),(104,1):(1,1,127),
              (124,0):(0,1,8),(124,1):(1,1,59),(127,0):(0,-1,124)}
    require({k:new[k]for k in old if old[k]!=new[k]}==expected,'exact six-row SF change')
    pred=lambda q:[(key,val)for key,val in old.items()if val[2]==q]
    require(pred(127)==[((110,0),(0,1,127))],'127 predecessor')
    require(pred(124)==[((104,1),(1,1,124))],'124 predecessor')
    require(pred(101)==[((96,0),(0,1,101))],'101 predecessor')
    require(set(pred(26))=={((11,0),(0,-1,26)),((101,0),(0,-1,26))},'26 predecessors')
    require(all(val[0]==0 for _,val in pred(11)),'all entries into11 write0')
    selector=dict(old)
    selector={k:(w,d,127 if n==124 else n)for k,(w,d,n)in selector.items()}
    selector.update({(127,0):(0,-1,124),(124,0):(0,1,8),(124,1):(1,1,59)})
    for q,hist in [(127,0),(124,1)]:
        for bit in [0,1]:
            ones=({-1}if hist else set())|({0}if bit else set())
            parent=run(old,(q,0,ones),1)
            parent=(127 if parent[0]==124 else parent[0],parent[1],parent[2])
            require(run(selector,(127,0,ones),3 if bit==0 else 1)==parent,'two-cell selector identity')
    count=0
    for bits in itertools.product([0,1],repeat=5):
        cells=dict(zip(range(-2,3),bits));ones={i for i,b in cells.items()if b}
        for q,admissible in [(101,cells[-1]==cells[0]==0),(26,cells[0]==1 and cells[1]==cells[2]==0)]:
            if admissible:
                require(run(selector,(q,0,ones),3)==run(new,(q,0,ones),1),'three-to-one whole window')
                count+=1
    require(count==12,'all admissible shortcut windows')
    return dict(changed_rows=6,selector_cases=4,shortcut_windows=count,
                complete_predecessors=True,relative_halt_witness_factor_each_direction=3)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path,required=True)
    ap.add_argument('--om',type=Path,required=True);ap.add_argument('--omf',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    data=[inspect(p,n,t)for p,n,t in [(args.parent,'AX11H',57922),(args.om,'OM',58014),(args.omf,'OMF',58010)]]
    require(data[0][2]==data[1][2]==data[2][2],'identical resolved instruction arrays')
    require(data[1][3]==data[2][3],'OM and OMF source address equality')
    changed=sum(x[0]!=y[0]for x,y in zip(data[0][3],data[1][3]));require(changed==154,'154 changed addresses')
    old,new=data[0][1],data[1][1]
    old_code={'00':104,'010':107,'011':98,'1':90}
    new_code={'0':104,'10':107,'110':98,'111':90}
    for code,target in old_code.items():require(prefix_reader(old,213,code)==target,'old operand reader')
    for code,target in new_code.items():require(prefix_reader(new,213,code)==target,'new operand reader')
    for code,target in {'00':213,'01':28,'10':77,'11':114}.items():require(prefix_reader(old,100,code)==target,'old MP reader')
    for code,target in {'0':213,'10':28,'110':77,'111':114}.items():require(prefix_reader(new,100,code)==target,'new MP reader')
    for bit in [0,1]:
        c=(69,0,{-1}if bit else set());duration=2 if bit else 3
        require(run(old,c,duration)==run(new,c,duration),'operand history-selector repair')
    sf=sf_cases(new,data[2][1])
    changes={k for k in new if new[k]!=data[2][1][k]}
    sf['all_changed_rows_seen_in_child_startup']=changes<=data[2][4]
    receipt=dict(status='PASS',machines=[x[0]for x in data],changed_addresses=changed,
                 source_graph_identical=True,operand_reader_cases=8,MP_reader_cases=8,
                 history_repair_cases=2,SF=sf,
                 uniform_proof='relative_om.tex; successful literal-contract replay remains a separate prerequisite')
    args.out.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
