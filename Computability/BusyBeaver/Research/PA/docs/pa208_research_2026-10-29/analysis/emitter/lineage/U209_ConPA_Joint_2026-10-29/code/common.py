"""Strict binary-table parsing, counting and deterministic serialization."""
from pathlib import Path
import hashlib,json

ROOT=Path(__file__).resolve().parents[1]
def need(ok,message):
    if not ok:raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def read(path):
    table={};starts=[]
    for line in Path(path).read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]))
        if not line or line.startswith('#'):continue
        fields=line.split();need(len(fields)==5,'Five transition fields required')
        q,b,w,d,z=fields;q,b,w,z=map(int,(q,b,w,z))
        need(q>=0 and z>=0 and b in(0,1) and w in(0,1) and d in('L','R'),'Row domain')
        need((q,b)not in table,'Duplicate row');table[q,b]=(w,1 if d=='R'else-1,z)
    need(starts==[0],'Start declaration');return table
def encode(table):
    return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(table.items()))).encode('ascii')
def census(table,count,halt=254):
    states={q for q,b in table}
    need(len(states)==count and len(table)==2*count,'State/row census')
    need(set(table)=={(q,b)for q in states for b in(0,1)},'Incomplete table')
    need(0 in states and halt not in states,'Start/halt collision')
    need({z for w,d,z in table.values()}-states=={halt},'Target closure')
    reached={0};queue=[0]
    for q in queue:
        for b in(0,1):
            z=table[q,b][2]
            if z!=halt and z not in reached:reached.add(z);queue.append(z)
    need(reached==states,'Graph-unreachable working state');return states
def compact(value):return(json.dumps(value,separators=(',',':'))+'\n').encode('ascii')
def write_json(path,value):Path(path).write_text(json.dumps(value,indent=2)+'\n')
def incoming(table,state):
    return [[q,b,w,d]for(q,b),(w,d,z)in sorted(table.items())if z==state]
