#!/usr/bin/env python3
"""Fixed, deterministic U212-to-U209 construction; no search or optimizer."""
import argparse,json
from pathlib import Path
from common import ROOT,need,read,encode,census,sha,compact,write_json,incoming
import source_language as L

PARENT_SHA='386ce16259d4c97e4af31b3ba494feaff11a0a1a066e0235dddc154b4cea38c4'
SOURCE_SHA='7b6539dc67b66ff73f22554018d7af5985d85574460a73fea5f025103c523d00'
TARGET={162:(207,203),203:(67,223),223:(153,188),188:(132,177),177:(155,89),
        89:(185,174),185:(159,181),181:(147,176),174:(98,129),129:(158,204),
        158:(218,178),204:(147,214),214:(146,216),216:(220,217),220:(218,176),
        217:(163,215),163:(90,211),215:(218,116)}
ROTATIONS=[(206,199,1),(205,206,1),(7,205,1)]
EXPECTED={'u209.native.tm':'d0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16',
          'u209.tm':'5ded628d692ff442e4346c61eb3db3c77b0ac2c80c1ecced45cbfc483be40e08',
          'sites.json':'cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164'}

def occurrences(root,table,target):
    found=[]
    def visit(node,q,path):
        if q==target:found.append((path,node));return
        if L.leaf(node):return
        for bit in(0,1):
            w,d,z=table[q,bit]
            if(w,d)==(bit,1):visit(node[bit],z,path+str(bit))
    visit(root,84,'');return found

def build(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    parent_raw=(ROOT/'baseline/u212.native.tm').read_bytes()
    source_raw=(ROOT/'baseline/sites.json').read_bytes()
    need(sha(parent_raw)==PARENT_SHA and sha(source_raw)==SOURCE_SHA,'Frozen parent identity')
    table=read(ROOT/'baseline/u212.native.tm');census(table,212);parent=table.copy()
    original=json.loads(source_raw);root=L.tree(original);old_graph=L.graph_intervals(original)
    need(L.graph_arithmetic(original)[0]==old_graph,'Parent source resolvers disagree')
    atoms=set(z for pair in TARGET.values()for z in pair)-set(TARGET)
    atom_nodes={}
    for q in sorted(atoms):
        places=occurrences(root,table,q)
        need(places and len({n for p,n in places})==1,f'Nonuniform atom {q}')
        atom_nodes[q]=places[0][1]
        need(L.boundary(atom_nodes[q])==(0,0,False),f'Nonclosed atom {q}')
    need(all(table[q,b][:2]==(b,1)for q in TARGET for b in(0,1)),'Non-pure retree node')
    external=[[q,b,w,d,z]for(q,b),(w,d,z)in sorted(table.items())if q not in TARGET and z in TARGET]
    need(external==[[156,1,1,1,162]],'Unexpected retree-region entrance')
    def factor_word(q,new=False,seen=()):
        need(q not in seen,'Cyclic decoder region')
        if q not in TARGET:need(q in atoms,'Unknown atomic continuation');return[q]
        a,b=TARGET[q]if new else(table[q,0][2],table[q,1][2])
        return factor_word(a,new,seen+(q,))+factor_word(b,new,seen+(q,))
    word=factor_word(162);need(word==factor_word(162,True),'Atomic word changed')
    def assemble(q):
        if q in atoms:return atom_nodes[q]
        a,b=TARGET[q];return assemble(a),assemble(b)
    replacement=assemble(162);places=occurrences(root,table,162)
    need(len(places)==1 and places[0][0]=='0011001110101011','Region occurrence')
    for path,node in places:
        need([r[1:]for r in L.sites(node)]==[r[1:]for r in L.sites(replacement)],'Primitive word changed')
        root=L.replace(root,path,replacement)
    for q,(a,b)in TARGET.items():table[q,0]=(0,1,a);table[q,1]=(1,1,b)
    rotation_records=[]
    for p,q,side in ROTATIONS:
        need(table[p,side]==(side,1,q),'Wrong rotation child')
        need(incoming(table,q)==[[p,side,side,1]],'Rotation inner reentry')
        need(all(table[x,b][:2]==(b,1)for x in(p,q)for b in(0,1)),'Rotation is not pure')
        occ=occurrences(root,table,p)
        need(occ and len({n for path,n in occ})==1,'Rotation occurrences differ')
        node=occ[0][1];a=node[0];b,c=node[1]
        need(all(L.boundary(n)==(0,0,False)for n in(a,b,c)),'Nonclosed rotation factor')
        x,y,z=table[p,0][2],table[q,0][2],table[q,1][2]
        table[p,0],table[p,1]=(0,1,q),(1,1,z)
        table[q,0],table[q,1]=(0,1,x),(1,1,y)
        for path,node in occ:root=L.replace(root,path,((a,b),c))
        rotation_records.append({'outer':p,'inner':q,'side':side,'paths':[path for path,n in occ]})
    need(table[171,0]==(0,-1,7),'Engine repair precondition');table[171,0]=(0,-1,205)
    sites=L.sites(root)
    need([r[1:]for r in sites]==[r[1:]for r in original],'Instruction sequence changed')
    need(L.graph_intervals(sites)==old_graph and L.graph_arithmetic(sites)[0]==old_graph,'Control graph changed')
    metrics=L.metrics(root)
    need(metrics=={'dag_nodes':197,'leaf_occurrences':3909,'maximum_depth':42,'maximum_zero_run':6},'Source metrics')
    prefold=table.copy();census(prefold,212)
    for keep,drop,helper in[(163,180,211),(220,181,129)]:
        for q,tag in[(keep,0),(drop,1)]:
            ins=incoming(table,q);need(ins and all(w==tag and d==1 for p,b,w,d in ins),'Fold tag premise')
        table={(q,b):(w,d,keep if z==drop else z)for(q,b),(w,d,z)in table.items()if q!=drop}
        table[keep,0]=(0,-1,helper)
    middle=table.copy();census(middle,210)
    inc218=incoming(table,218)
    need(inc218==[[158,0,0,1],[211,0,0,1],[215,0,0,1]],'Final predecessor-zero invariant')
    table={(q,b):(w,d,157 if z==218 else z)for(q,b),(w,d,z)in table.items()if q!=218}
    states=census(table,209);mapping={q:i for i,q in enumerate(sorted(states))};mapping[254]=209
    dense={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in table.items()};census(dense,209,209)
    reverse={v:k for k,v in mapping.items()}
    need({(reverse[q],b):(w,d,reverse[z])for(q,b),(w,d,z)in dense.items()}==table,'Relabeling mismatch')
    outputs={'prefold212.native.tm':encode(prefold),'doublefold210.native.tm':encode(middle),
             'u209.native.tm':encode(table),'u209.tm':encode(dense),'sites.json':compact(sites)}
    for name,digest in EXPECTED.items():need(sha(outputs[name])==digest,'Candidate bytes differ: '+name)
    for name,data in outputs.items():(output/name).write_bytes(data)
    write_json(output/'state_map.json',{'native_to_dense':mapping,'dense_to_native':reverse,'native_halt':254,'dense_halt':209})
    report={'status':'DETERMINISTIC_CONSTRUCTION_PASS','working_states':209,'transition_rows':418,
      'start':0,'halt':209,'native_halt':254,'target_pairs':TARGET,'closed_factor_word':word,
      'factor_sizes':[len(L.sites(atom_nodes[q]))for q in word],'retree_region_ordinal_interval':[640,3736],
      'region_external_incoming':external,'rotations':rotation_records,'engine_repair':[171,0,0,-1,205],
      'deletions':[[180,163],[181,220],[218,157]],'metrics':metrics,
      'changed_addresses':sum(a[0]!=b[0]for a,b in zip(original,sites)),
      'changed_retained_rows':sum(parent[k]!=v for k,v in table.items()),
      'removed_rows':sorted(set(parent)-set(table)),'incoming218_before_deletion':inc218,
      'parent_sha256':PARENT_SHA,'parent_source_sha256':SOURCE_SHA,
      'sha256':{name:sha(data)for name,data in outputs.items()}}
    write_json(output/'construction.json',report);return report

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'build/machine');a=p.parse_args()
    print(json.dumps(build(a.output),indent=2))
