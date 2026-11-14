"""Strict canonical I/O for finite binary Turing-machine transition tables."""
def require(ok,why):
    if not ok:raise ValueError(why)

def parse(raw,halt=254):
    T={};starts=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start'):
            require(line=='#! start 0','Invalid start header');starts.append(0)
        elif line.strip() and not line.startswith('#'):
            fields=line.split();require(len(fields)==5,'Wrong row width')
            q,b,w,d,z=fields;q,b,w,z=map(int,(q,b,w,z))
            require(q>=0 and z>=0 and b in(0,1)and w in(0,1)and d in('L','R'),'Invalid row')
            require((q,b)not in T,'Duplicate row');T[q,b]=(w,1 if d=='R'else -1,z)
    require(starts==[0],'Missing or repeated start')
    Q={q for q,b in T}
    require(0 in Q and halt not in Q,'Invalid start/halt')
    require(set(T)=={(q,b)for q in Q for b in(0,1)},'Incomplete binary table')
    require({z for w,d,z in T.values()}-Q=={halt},'Invalid targets')
    reached={0};todo=[0]
    for q in todo:
        for bit in(0,1):
            z=T[q,bit][2]
            if z!=halt and z not in reached:reached.add(z);todo.append(z)
    require(reached==Q,'Graph-unreachable working state')
    return T

def encode(T):
    return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))).encode('ascii')
