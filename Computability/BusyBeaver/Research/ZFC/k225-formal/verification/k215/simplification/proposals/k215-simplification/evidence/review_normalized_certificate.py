#!/usr/bin/env python3
"""Independent read-only audit of the normalized source bisimulation.

Uses string paths and direct DAG interpretation, without importing the
certificate generator, graph-compression code, or upstream gen_cert module.
"""
from pathlib import Path
from collections import Counter,deque
import argparse,json,hashlib

PIN='b6c7087477e51c017003bd729e712c8969733223'
SOURCE_PATH=Path('Computability/BusyBeaver/Research/ZFC/candidate-k215/sites215.json')
SOURCE_SHA256='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
DAG_SHA256='227d316cd61ce4781405c5abbd53e9f206bc70111c6c7f9237ecf7baf0a8517a'
DAG_BLOB='ad1775396daf0d351492a8d95c3af1d95bc33ea1'
ops={'CI':'EInc','CD':'EDecnz','CB':'EBreak','CC':'EContinue','CH':'EHalt'}
src={}
dag={}

def padded(path,depth):return (path+'0'*depth)[:depth]

def observe(which,path):
    if which==0:
        prefix=''
        for d in range(1,489):
            prefix+=path[d-1]if d<=len(path)else'0'
            if prefix in src:return src[prefix],prefix
        raise ValueError('source decoder did not reach leaf')
    n=0
    for d in range(1,dag['nnodes']+2):
        b=int(path[d-1])if d<=len(path)else 0
        op,arg=dag['nodes'][str(n)][b]
        if op!='N':return(op,arg),padded(path,d)
        n=arg
    raise ValueError('DAG decoder exhausted')

def inc(path):
    if not path:return''
    return f'{(int(path,2)+1)%(1<<len(path)):0{len(path)}b}'

def strip(path,bit,k):
    for i in range(len(path)-1,-1,-1):
        if path[i]==bit:
            k-=1
            if k==0:return path[:i]
    return''

def seg(which,path):
    counts=Counter()
    for _ in range(1000):
        (op,r),consumed=observe(which,path)
        if op in('EDecnz','EHalt'):return counts,path
        if op=='EInc':counts[r]+=1;path=inc(consumed)
        elif op=='EBreak':path=inc(strip(consumed,'0',r))
        elif op=='EContinue':path=strip(consumed,'1',r)
        else:raise ValueError(op)
    raise ValueError('segment fuel exhausted')

def audit(packet,repo=None):
    global src,dag
    P=Path(packet).resolve()
    S=P/'upstream/sites215.json'
    source_raw=S.read_bytes()
    assert hashlib.sha256(source_raw).hexdigest()==SOURCE_SHA256
    src={p:(ops[o],a)for p,o,a in json.loads(source_raw)}
    dag=json.loads((P/'upstream/dagperm_nodes.json').read_text())
    if repo is not None:
        assert source_raw==(Path(repo)/SOURCE_PATH).read_bytes()
    wire=json.loads((P/'normalized_certificate.json').read_text())
    assert wire['source_commit']==PIN
    assert wire['schema']=='K215-normalized-source-bisim-v1'
    assert wire['inputs']=={'sites215.json':SOURCE_SHA256,'dagperm_nodes.json':DAG_SHA256}
    oldmap=json.loads((P/'old_to_normalized.json').read_text())
    decode=lambda x:bin(int(x))[3:]
    entries=[(decode(a),decode(b),j,k)for a,b,j,k in wire['entries']]
    assert len(entries)==1426 and len(set((a,b)for a,b,j,k in entries))==1426
    assert all(not a.endswith('0')and not b.endswith('0')for a,b,j,k in entries)
    assert all(1<=int(a)<1<<513 and 1<=int(b)<1<<513 for a,b,_,_ in wire['entries'])
    branchcount=0;decs=halt=0;maxraw=0
    def checkbranch(a,b,j):
        nonlocal branchcount,maxraw
        assert 0<=j<len(entries)
        xs,a=seg(0,a);ys,b=seg(1,b);assert xs==ys
        maxraw=max(maxraw,len(a),len(b));branchcount+=1
        for which,p in[(0,a),(1,b)]:
            e,c=observe(which,p)
            assert e[0]in('EDecnz','EHalt')
            assert p.rstrip('0')==c.rstrip('0')
            assert observe(which,p)==observe(which,p.rstrip('0'))
        assert(a.rstrip('0'),b.rstrip('0'))==entries[j][:2]
    checkbranch('','',0)
    for a,b,j,k in entries:
        (op,r),aa=observe(0,a);(oq,s),bb=observe(1,b)
        assert aa.rstrip('0')==a and bb.rstrip('0')==b
        if op==oq=='EHalt':halt+=1
        else:
            assert op==oq=='EDecnz'and r==s;decs+=1
            checkbranch(inc(aa),inc(bb),j)
            checkbranch(inc(strip(aa,'0',1)),inc(strip(bb,'0',1)),k)
    # Independently reconstruct the old literal-pointer pair graph in BFS order.
    old=[];ids={};todo=deque()
    def oldtarget(a,b):
        xs,a=seg(0,a);ys,b=seg(1,b);assert xs==ys
        pair=a,b
        if pair not in ids:ids[pair]=len(old);old.append([a,b,None,None]);todo.append(pair)
        return ids[pair]
    assert oldtarget('','')==0
    while todo:
        a,b=todo.popleft();i=ids[a,b]
        (op,r),aa=observe(0,a);(oq,s),bb=observe(1,b)
        if op==oq=='EHalt':old[i][2:]=[0,0]
        else:
            assert op==oq=='EDecnz'and r==s
            old[i][2]=oldtarget(inc(aa),inc(bb))
            old[i][3]=oldtarget(inc(strip(aa,'0',1)),inc(strip(bb,'0',1)))
    assert len(old)==2240 and len(oldmap)==2240
    assert set(oldmap)==set(range(1426))
    fibers=Counter(oldmap)
    for i,(a,b,j,k)in enumerate(old):
        row=entries[oldmap[i]]
        assert row[:2]==(a.rstrip('0'),b.rstrip('0'))
        assert row[2:]==(oldmap[j],oldmap[k])
    assert(decs,halt,branchcount)==(1425,1,2851)
    for name,digest in wire['inputs'].items():
        assert hashlib.sha256((P/'upstream'/name).read_bytes()).hexdigest()==digest
    raw=(P/'upstream/dagperm_nodes.json').read_bytes()
    assert hashlib.sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest()==DAG_BLOB
    return {'status':'INDEPENDENT_STRING_PATH_AUDIT_PASS','source_commit':PIN,'literal_entries':len(old),'normalized_entries':len(entries),'decrement_entries':decs,'halt_entries':halt,'branches':branchcount,'removed_entries':len(old)-len(entries),'surjective_successor_map':True,'maximum_fiber':max(fibers.values()),'fiber_histogram':dict(sorted(Counter(fibers.values()).items())),'maximum_normalized_path_bits':max(max(len(a),len(b))for a,b,j,k in entries),'zero_offset_verified_by_equal_effects':True,'canonical_source_bytes_verified':True,'source_sha256':SOURCE_SHA256,'canonical_dag_blob_verified':True,'dag_git_blob':DAG_BLOB,'repository_source_bytes_compared':repo is not None,'source_verification_scope':'Pinned SHA-256 and Git blob identities for packaged inputs; additionally byte-compared source against supplied repository.'if repo is not None else'Pinned SHA-256 and Git blob identities for packaged inputs; no local repository comparison requested.','independent_implementation':'No imports from generator or graph-compression modules; direct source trie, direct DAG, string-path arithmetic and independent BFS.','scope':'Finite certificate and source correspondence audit only; no Lean compilation is performed by this script.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent.parent/'source_normalization',help='Normalized source packet (default: ../source_normalization relative to this script).')
    parser.add_argument('--repo',type=Path,help='Optional ProveIt checkout for an additional exact source-byte comparison.')
    parser.add_argument('--output',type=Path,help='Optional result JSON path; default prints only and does not overwrite saved receipts.')
    args=parser.parse_args()
    result=audit(args.packet,args.repo)
    rendered=json.dumps(result,indent=2)+'\n'
    if args.output is not None:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(rendered)
    print(rendered,end='')

if __name__=='__main__':main()
