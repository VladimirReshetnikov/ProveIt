#!/usr/bin/env python3
"""Independent finite reconstruction of retained compact44 recipe and masks."""
import ast,gzip,hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-selector-recipe-check'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    for name in ('README.md','check.py','observations.json'):
        p=PKG/name;b=subprocess.run(['git','show','b2f2f495e3:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+name)
    spec=importlib.util.spec_from_file_location('recipe_check',PKG/'check.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    for path,h in mod.PINS.items():need(sha(path)==h,'pinned input '+str(path))
    binding=json.loads(mod.BINDING.read_text());rows=json.loads(mod.JSON.read_text());need(len(rows)==943 and rows[0]==[2,435,3,1] and rows[1]==[5,0,0,0],'table')
    names=('OFFSETS','WIDTHS','ANCHORS','BARE');constants={}
    for node in ast.parse(mod.BUILDER.read_text()).body:
        if isinstance(node,ast.Assign):
            for target in node.targets:
                if isinstance(target,ast.Name) and target.id in names:need(target.id not in constants,'duplicate builder constant');constants[target.id]=ast.literal_eval(node.value)
    need(set(constants)==set(names),'missing constants');offsets,widths,anchors,bare=(constants[n] for n in names)
    need(binding['L']==8807 and binding['b']==67 and binding['d']==590069 and binding['port_widths']==list(widths) and binding['anchors']==list(anchors),'binding')
    slots=[None]*41
    for field,indices in enumerate(binding['binary_positions']):
        need(len(indices)==widths[field],'field width')
        for j,k in enumerate(indices):need(type(k) is int and 0<=k<41 and slots[k] is None,'slot duplicate');slots[k]=offsets[field]+j
    for k,p in zip(binding['anchor_positions'],anchors):need(type(k) is int and 0<=k<41 and slots[k] is None,'anchor duplicate');slots[k]=p
    need(None not in slots and len(set(slots))==41 and all(0<=x<8807 for x in slots),'slots')
    vals=[w+(n<<8)+(e<<17)+(s<<25)+(127<<34) for w,n,e,s in rows]
    need(all(0<v<1<<41 for v in vals),'payload range')
    ce={i:1+(1<<10)*((1<<41)-v) for i,v in enumerate(vals)}
    for j,p in enumerate(slots):need(p not in ce,'slot overlaps selector');ce[p]=1<<(10+j)
    for p in (1063,1064):need(p not in ce,'dummy overlaps support');ce[p]=0
    E=set(ce);need(len(E)==986 and E==set(range(943))|set(slots)|{1063,1064},'support union')
    rho=1<<67;B=1<<590069;beta=B-1
    mc=beta-sum(1<<(67*e) for e in E if e!=1)-(2<<(67*1063))
    dc={e:1 for e in bare}
    for e,c in ce.items():
        if c:
            for t in (4393,5495):dc[t-e]=dc.get(t-e,0)+c
    K=sum(c<<(67*e) for e,c in dc.items())+(1<<(590069+67*42))
    mu=(1<<51)-2;targets=[*range(1013,1023),*range(1065,1074),2195,3296];padding={e:(1<<65)-1 for e in range(8792,8805)};padding[8805]=(1<<19)-1
    high={0:4,4393:mu,5495:mu}
    for x in targets:high[x]=high.get(x,0)+1
    for x,c in padding.items():high[x]=high.get(x,0)+c
    need(all(0<=x<rho for x in high.values()),'high digit range');mf=sum(v<<(67*i) for i,v in high.items())
    decoded={}
    for name,file,value in [('beta',mod.BETAFILE,beta),('K',mod.KFILE,K),('MC',mod.MCFILE,mc),('MF_source',mod.MFFILE,mf+beta)]:
        raw=gzip.decompress(file.read_bytes());need(int.from_bytes(raw,'little')==value,'materialized '+name);decoded[name]=hashlib.sha256(raw).hexdigest()
    need(0<mc<beta<mf+beta<2*beta and mc.bit_count()+mf.bit_count()==590069,'tuple bounds/population')
    for j in range(8807):
        a=(mc>>(67*j))&(rho-1);b=(mf>>(67*j))&(rho-1)
        need(a==rho-1-int(j in E and j!=1)-(2 if j==1063 else 0) and b==high.get(j,0),'digit '+str(j))
    support=lambda t:{(t-e)%8807 for e in E}
    need(not(support(4393)&support(5495)) and support(2195)&support(3296)=={0} and not(support(4392)&support(5494)) and not(support(4392)&support(5495)) and support(4393)&support(5494)=={2198},'support intersections')
    chosen=[0,0]
    for phase in range(8807):
        valid=[i for i,t in enumerate((4393,5495)) if (t-phase)%8807 not in E and (t-1-phase)%8807!=1063]
        need(valid,'no finite target '+str(phase));chosen[valid[0]]+=1
    M=(len(E)+2)*(2*sum(ce.values())+6);need(4*M+8<rho<12*M+8,'carry slack')
    local=(1<<51)-(1<<10);temporal=1<<10;need(local&mu and not ((local+temporal)&mu),'counterexample')
    good=subprocess.run([sys.executable,'-I','-S',str(PKG/'check.py'),'--negative-controls'],capture_output=True,text=True,timeout=60)
    bad=subprocess.run([sys.executable,'-O','-I','-S',str(PKG/'check.py')],capture_output=True,text=True,timeout=30)
    need(good.returncode==0 and not good.stderr and 'PASS_REJECTED_MUTATED_SELECTOR' in good.stdout and 'PASS_REJECTED_MUTATED_COPY' in good.stdout and bad.returncode!=0 and 'optimized Python rejected' in bad.stderr,'author controls')
    for path,h in mod.PINS.items():need(sha(path)==h,'post input drift '+str(path))
    print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_FINITE_RECIPE_AUDIT','source_commit':'b2f2f495e3','rows':943,'copy_positions':41,'support':len(E),'digits_per_mask':8807,'phase_cases':8807,'phase_choices':chosen,'decompressed_sha256':decoded,'rho':rho,'M':M,'author_controls_exit':good.returncode,'optimized_exit':bad.returncode,'scope':'Finite external integer reconstruction only; no actual model temporal transport, graph port binding, machine simulation, checker calibration or iPRA proof.'},indent=2))
if __name__=='__main__':main()
