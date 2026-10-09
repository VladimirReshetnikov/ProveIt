"""Independent literal controls and reproducible relation generators."""
from collections import Counter, deque
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))


def literal(size, rows, ports):
    parent = list(range(size))
    def root(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for a,b,c,d,sign in rows:
        for x in range(a,b+1):
            y = x+c-a if sign == 1 else a+d-x
            parent[root(x)] = root(y)
    masks = {root(x): 0 for x in range(size)}
    for i,port in enumerate(ports):
        for lo,hi in port:
            for x in range(lo,hi):
                masks[root(x)] |= 1 << i
    return dict(Counter(masks.values()))


def literal_signed(size, rows, ports):
    adjacency = [[] for _ in range(size)]
    for a,b,c,d,sign,parity in rows:
        for x in range(a,b+1):
            y = x+c-a if sign == 1 else a+d-x
            adjacency[x].append((y,parity)); adjacency[y].append((x,parity))
    mark = [0]*size
    for i,port in enumerate(ports):
        for lo,hi in port:
            for x in range(lo,hi): mark[x] |= 1 << i
    labels = {}
    answer = {}
    for start in range(size):
        if start in labels: continue
        labels[start] = 0; todo=[start]; mask=0; good=True
        while todo:
            x=todo.pop(); mask |= mark[x]
            for y,p in adjacency[x]:
                expected=labels[x]^p
                if y in labels:
                    good &= labels[y] == expected
                else:
                    labels[y]=expected;todo.append(y)
        answer.setdefault(mask,[0,0])[0 if good else 1] += 1
    return answer


def random_case(rng, max_size=35, max_rank=8):
    size = rng.randrange(max_size+1)
    rows = []
    if size:
        for _ in range(rng.randrange(10)):
            width=rng.randrange(1,size+1)
            a=rng.randrange(size-width+1);c=rng.randrange(size-width+1)
            rows.append([a,a+width-1,c,c+width-1,rng.choice((-1,1))])
    ports=[]
    for _ in range(rng.randrange(max_rank+1)):
        port=[]
        for _ in range(rng.randrange(4)):
            a,b=sorted((rng.randrange(size+1),rng.randrange(size+1)))
            port.append([a,b])
        ports.append(port)
    return size,rows,ports


def parallel_chain(copies=1 << 500, blocks=8, rank=8, shape='disjoint'):
    size=blocks*copies
    rows=[[i*copies,(i+1)*copies-1,(i+1)*copies,(i+2)*copies-1,1]
          for i in range(blocks-1)]
    if shape == 'coincident':
        ports=[[(0,copies//2)] for _ in range(rank)]
    elif shape == 'nested':
        ports=[[(0,(i+1)*copies//rank)] for i in range(rank)]
    else:
        ports=[[(i*copies//rank,(i+1)*copies//rank)] for i in range(rank)]
    return size,rows,ports
