#!/usr/bin/env python3
"""Independent bounded-array startup and lexicographic source-prefix audit.

No imports from the source compiler, symbolic runtime, or primary bootstrap
checker. This proves only the exact finite startup and 177-step source bridge.
"""
import argparse,bisect,gzip,hashlib,json
from pathlib import Path

def sha(raw):return hashlib.sha256(raw).hexdigest()
def need(ok,message):
    if not ok:raise ValueError(message)
def table(raw):
    T={};start=None
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):start=int(line[9:]);continue
        if not line or line.startswith('#'):continue
        q,r,w,d,z=line.split();q,r,w,z=map(int,(q,r,w,z))
        need((q,r)not in T and r in(0,1)and w in(0,1)and d in('L','R'),'Invalid row')
        T[q,r]=(w,1 if d=='R'else -1,z)
    need(start==0 and len(T)==430,'Expected GC215 start/table census')
    return T

def run_binary(T,deltas=None):
    # A checked finite bound, with zero exterior. Every read/write is bounds-
    # checked; no inference is made from unvisited tape cells.
    cells=bytearray(4096);offset=2048;head=0;state=0;low=high=0
    for tick in range(68710):
        need(0<=head+offset<len(cells),'Finite replay bound exceeded')
        read=cells[head+offset];write,move,target=T[state,read]
        if deltas is not None:
            need(deltas[tick]==[tick,state,head,read,write,move,target],'Saved delta differs')
        cells[head+offset]=write;head+=move;state=target
        low=min(low,head);high=max(high,head)
    ones={i-offset for i,v in enumerate(cells)if v}
    return state,head,ones,low,high

def run_source(rows,saved):
    paths=[p for p,op,arg in rows];need(len(rows)==4732,'Source census')
    depth=max(map(len,paths));cursor=0
    for p,op,arg in rows:
        need(set(p)<=set('01') and p,'Invalid path')
        left=int(p,2)<<(depth-len(p));right=(int(p,2)+1)<<(depth-len(p))
        need(left==cursor,'Source leaves are not a full ordered prefix code');cursor=right
        need(op in('CI','CD','CB','CC','CH'),'Invalid primitive')
    need(cursor==1<<depth,'Source is incomplete')
    pc=25;registers=[1,0,2,0,0,0,0,0,0];trace=[]
    for tick in range(177):
        p,op,arg=rows[pc];oldpc=pc;before=registers.copy();after=(pc+1)%len(rows)
        if op=='CI':registers[arg]+=1;pc=after
        elif op=='CD'and registers[arg]>0:registers[arg]-=1;pc=after
        else:
            need(op in('CD','CB','CC'),'Unexpected primitive in source bridge')
            edge='1'if op=='CC'else'0';count=1 if op=='CD'else arg
            positions=[i for i,b in enumerate(p)if b==edge]
            prefix=p[:positions[-count]] if len(positions)>=count else''
            # All words with prefix r precede r+'2' in lexicographic order.
            if op=='CC':pc=bisect.bisect_left(paths,prefix)
            else:pc=bisect.bisect_left(paths,prefix+'2')%len(rows)
        trace.append(dict(step=tick,ordinal=oldpc,site=rows[oldpc],before=before,
                          next_ordinal=pc,after=registers.copy()))
    need(trace==saved,'Saved source trace differs from lexicographic execution')
    need(pc==58 and registers==[1,0,0,0,0,0,0,18,0],'Source bridge endpoint')
    return paths[pc],registers

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--native',type=Path,required=True);p.add_argument('--dense',type=Path,required=True)
    p.add_argument('--source',type=Path,required=True);p.add_argument('--evidence',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    nr=a.native.read_bytes();dr=a.dense.read_bytes();sr=a.source.read_bytes()
    need(sha(nr)=='a5d8dfeb92a6ae843692c65b5eaf69b845b08b48d65dc011ba8a457e4faec67d','Final native hash')
    need(sha(dr)=='ccabf998e346356edb33a829a8c2ab7a24b69f032349e9228f53e2295337ec0f','Final dense hash')
    need(sha(sr)=='3b4e8203227f4be6d868ffdfb8d1a6311f5ac9a647dadf8386eb8f0de509ce57','Final source hash')
    bootstrap=json.loads((a.evidence/'bootstrap.json').read_bytes())
    delta=gzip.decompress((a.evidence/'blank-delta.jsonl.gz').read_bytes())
    source_raw=(a.evidence/'AX-prefix.json').read_bytes()
    need(sha(delta)==bootstrap['delta_sha256'] and sha(source_raw)==bootstrap['AX_prefix_sha256'],'Trace hashes')
    ds=[json.loads(x)for x in delta.splitlines()];need(len(ds)==68710,'Delta count')
    address,logical=run_source(json.loads(sr),json.loads(source_raw))
    # Construct the whole frame independently from its components.
    frame={-3,62}|{-2+i for i,b in enumerate(address)if b=='1'}
    physical=[logical[i]for i in(2,8,1,4,3,7,0,5,6)]
    position=63
    for value in physical+[0]*63:
        need(position not in frame,'Overlapping frame component')
        frame.update(position+i for i in range(1,value+2));position+=value+2
    native=run_binary(table(nr),ds);dense=run_binary(table(dr))
    need(native[:3]==(84,-2,frame),'Native whole-frame endpoint')
    need(dense[:3]==(81,-2,frame),'Dense whole-frame endpoint')
    need(frame==set(bootstrap['one_cells'])and len(frame)==100,'Recorded entire tape differs')
    result=dict(status='INDEPENDENT_ARRAY_STARTUP_AND_LEXICOGRAPHIC_SOURCE_PASS',
        binary_steps=68710,source_steps=177,native_dispatcher=84,dense_dispatcher=81,
        head=-2,header=62,source_ordinal=58,source_address=address,
        logical_registers=logical,spares=63,one_cells=100,visited_head_interval=list(native[3:]),
        native_sha256=sha(nr),dense_sha256=sha(dr),source_sha256=sha(sr),
        checked_saved_deltas=len(ds),checked_saved_source_records=177,
        implementation='Standard library only. Bounded bytearray literal TM replay; independent lexicographic cut resolution; whole finite tape equality.',
        scope='Finite blank initialization and AX source prefix only. Universal runtime, source-command calibration and logic remain separate obligations.',
        checker_sha256=sha(Path(__file__).read_bytes()))
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
