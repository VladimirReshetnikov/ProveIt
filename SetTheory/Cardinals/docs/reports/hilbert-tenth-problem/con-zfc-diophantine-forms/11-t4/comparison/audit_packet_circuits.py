"""Independently recount received JSON data. No repository code is executed."""
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parent
P=1_000_000_007
def tidy(a):
    while len(a)>1 and not a[-1]:a.pop()
    return a
def add(a,b,sgn=1):
    c=[0]*max(len(a),len(b))
    for j,x in enumerate(a):c[j]+=x
    for j,x in enumerate(b):c[j]+=sgn*x
    return tidy([x%P for x in c])
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        for k,y in enumerate(b):c[j+k]=(c[j+k]+x*y)%P
    return tidy(c)
def walk(a,path=''):
    if isinstance(a,dict):
        if isinstance(a.get('source'),list) and all(isinstance(x,list) and len(x)==4 for x in a['source']):yield path,a
        else:
            for k,v in a.items():yield from walk(v,path+'/'+k)
    elif isinstance(a,list):
        for k,v in enumerate(a):yield from walk(v,path+'/'+str(k))
receipt=[]
for file in sorted((HERE/'sources').rglob('*.json')):
    root=json.loads(file.read_text())
    for path,packet in walk(root):
        source=packet['source']
        variables=packet.get('witnesses',packet.get('positive_witnesses'))
        if variables is None:continue
        variables=set(variables)
        produced={row[0] for row in source}
        free={v for row in source for v in row[2:] if isinstance(v,str) and v not in produced}
        free.update(packet.get('fixed_numerals',[]))
        cmp=packet.get('comparisons',packet.get('equations'))
        if isinstance(cmp,list):
            free.update(v for pair in cmp for v in pair if isinstance(v,str) and v not in produced)
        consts=sorted(free-variables)
        e={v:[5+2*j,3+5*j] for j,v in enumerate(sorted(variables))}
        e.update({v:[19+4*j] for j,v in enumerate(consts)})
        for name,op,x,y in source:
            assert name not in e and op in ('+','-','*')
            a=[x%P] if isinstance(x,int) else e[x]
            b=[y%P] if isinstance(y,int) else e[y]
            e[name]=mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
        comparisons=packet.get('comparisons',packet.get('equations'))
        output=packet.get('output')
        if output:
            degrees=[len(e[output])-1]
        elif isinstance(comparisons,list):
            degrees=[]
            for x,y in comparisons:
                a=[x] if isinstance(x,int) else e[x]
                b=[y] if isinstance(y,int) else e[y]
                degrees.append(len(add(a,b,-1))-1)
        else:continue
        receipt.append({'file':str(file.relative_to(HERE)),'packet_path':path,
             'variables':len(variables),'equations':len(degrees),'operations':len(source),
             'multiplications':sum(row[1]=='*' for row in source),
             'additions_subtractions':sum(row[1]!='*' for row in source),
             'line_specialization_degrees':degrees,'max_line_degree':max(degrees),
             'source_file_sha256':hashlib.sha256(file.read_bytes()).hexdigest()})
out={'scope':'Static recount and finite-field line-degree lower bounds, not a uniform symbolic degree proof or proof of semantic equivalence. No downloaded code executed.', 'results':receipt}
(HERE/'PACKET_CIRCUIT_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
for row in receipt:print(row['file'].split('/')[1],row['packet_path'],f"v{row['variables']} e{row['equations']} ops{row['operations']} degree{row['max_line_degree']}")
