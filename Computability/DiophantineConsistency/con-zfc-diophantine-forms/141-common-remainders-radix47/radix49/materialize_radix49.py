"""Build the complete coherent radix49 tuple and specialize the P66 circuit."""
from pathlib import Path
from collections import Counter
import base64,gzip,hashlib,json,math
from radix_probe import decode_tiles,coefficients,residues,require,prime,factors,order,L,MARKERS

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'radix49'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(path,obj):path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')

def old_coefficient_route():
    parent=ROOT/'sources/research/indexed-tile-enumeration/coefficients'
    enc=(parent/'K.bin.gz.base64').read_text()
    comp=base64.b64decode(enc)
    binding=json.loads((parent/'BINDING.json').read_text())['ports']['K0']
    require(sha(comp)==binding['gzip_sha256'],'old gzip checksum')
    raw=gzip.decompress(comp)
    require(sha(raw)==binding['raw_sha256'],'old raw checksum')
    K=int.from_bytes(raw,'little')
    require(K.bit_length()==binding['bits'],'old bit count')
    bare=sum(1<<(67*e) for e in [30,62,1100,2201,8849])
    reversed_phi,rem=divmod(K-bare,(1<<(67*1097))+(1<<(67*2199)))
    require(rem==0,'exact old K factorization')
    c=[];mask=(1<<67)-1
    for i in range(3297):
        c.append(reversed_phi&mask);reversed_phi>>=67
    require(reversed_phi==0,'exact old factor length')
    c.reverse()
    require(c==coefficients(decode_tiles(),False),'old K vs all typed coefficients')
    for e in MARKERS:c[e]=1<<44
    return c,{'old_K_raw_sha256':sha(raw),'old_K_gzip_sha256':sha(comp),'old_K_bits':K.bit_length(),'exact_factor_remainder':rem}

def tuple_values(b,c,kind):
    power=lambda e:1<<(b*e)
    B=power(L);rho=1<<b;beta=B-1
    E=set(i for i,v in enumerate(c) if v)|{1063,1064}
    require(len(E)==986,'full physical support')
    K=sum(power(e) for e in [30,62,1100,2201,8849])+sum(ce*(power(4393-e)+power(5495-e)) for e,ce in enumerate(c) if ce)
    MC=beta-sum(power(e) for e in E if e!=1)-2*power(1063)
    core=sum(power(e) for e in range(1013,1023))+sum(power(e) for e in range(1065,1074))+power(2195)+power(3296)
    if kind=='shared49':
        mu=(1<<47)-2
        Z=(rho-1)*sum(power(e) for e in range(8792,8807))+(rho-1)*(power(7691)+power(7692))+((1<<41)-4)*power(7693)
        require(Z==B-power(8792)+((1<<41)-3)*power(7693)-power(7691),'two padding spellings')
    elif kind=='old55':
        mu=(1<<51)-2
        Z=B-power(8792)+((1<<41)-4)*power(7691)
    elif kind=='old53':
        # Same full15-field tail; remaining69 tests occupy53+16 fields.
        mu=(1<<51)-2
        Z=B-power(8792)+(rho-1)*power(7691)+((1<<18)-4)*power(7692)
    else:raise ValueError(kind)
    MF_native=4+mu*(power(4393)+power(5495))+core+Z
    MF=MF_native+beta
    require(beta%2==1 and 0<MC<beta<MF<2*beta,'scalar coefficient box')
    require(MC%4==2 and MF_native%8==4,'origin residues')
    require(MC.bit_count()==b*L-986 and MF_native.bit_count()==986,'population identity')
    return {'beta':beta,'K0':K,'MC':MC,'MF':MF},MF_native,E

def polynomial_metrics(p):
    rows=p['source']; known=set(p['witnesses'])|set(p['fixed_numerals']);deps={};deg={v:1 for v in p['witnesses']};deg.update({v:0 for v in p['fixed_numerals']})
    for out,op,a,b in rows:
        require(out not in known,'unique circuit name')
        require(op in ['+','-','*'],'valid op')
        for x in [a,b]:require(type(x) is int or x in known,'bound circuit input')
        da=0 if type(a)is int else deg[a];db=0 if type(b)is int else deg[b]
        deg[out]=da+db if op=='*' else max(da,db)
        deps[out]=[x for x in [a,b] if type(x)is str];known.add(out)
    live=set();stack=[p['output']]
    while stack:
        v=stack.pop()
        if v in live:continue
        live.add(v);stack+=deps.get(v,[])
    require(all(r[0] in live for r in rows),'no dead gates')
    require(set(p['witnesses'])<=live,'no dead witnesses')
    return {'operations':len(rows),'operation_counts':dict(Counter(r[1] for r in rows)),'syntactic_degree':deg[p['output']],'all_witnesses_live':True,'all_gates_live':True}

def main():
    OUT.mkdir(exist_ok=True);(OUT/'coefficients').mkdir(exist_ok=True)
    c=coefficients(decode_tiles(),True)
    c2,old=old_coefficient_route()
    require(c==c2,'independent full3297 changed-array agreement')
    dump(OUT/'phi_coefficients.json',c)
    values,mfn,E=tuple_values(49,c,'shared49')
    binding={}
    for name,value in values.items():
        raw=value.to_bytes((value.bit_length()+7)//8,'little')
        blob=gzip.compress(raw,compresslevel=9,mtime=0)
        path=OUT/'coefficients'/(name+'.bin.gz');path.write_bytes(blob)
        binding[name]={'file':'coefficients/'+path.name,'bits':value.bit_length(),'raw_bytes':len(raw),'raw_sha256':sha(raw),'gzip_bytes':len(blob),'gzip_sha256':sha(blob)}
    cert=json.loads((ROOT/'radix_probe_result.json').read_text())[0]
    require(cert['outcome']=='found','controller closed')
    for m in [7,49,8807,cert['selected']['candidate']]:
        modular=residues(49,c,m)
        require(values['K0']%m==modular['K'],'full K agrees modular')
        B=values['beta']+1
        require((1+B*values['K0']+B*B)%m==modular['Hctrl'],'full bracket agrees modular')
    p=json.loads((ROOT/'sources/candidates/one-page-compact66-radix55/polynomial.json').read_text())
    p['name']='shared_marker_radix49_p66_degree157'
    p['coefficient_binding']={'schema':'whole_shared_marker_radix49_p66_binding_v1','ports':binding,'raw_bytes':sum(x['raw_bytes'] for x in binding.values()),'tuple':'all four coherent49 ports; shared seven physical markers; MF shifted exactly once'}
    p['proof']='radix49_completion.md'
    p['proof_boundary']='Ordinary pinned conditional49 native/P66 proof, now with explicit independently checked controller and full coefficient tuple; inherited syntactic-refutation calibration; no new Lean derivation.'
    metrics=polynomial_metrics(p)
    require(metrics['operations']==66 and metrics['syntactic_degree']==161,'P66 circuit profile')
    # N1 cancels its two degree22 terms; the displayed expanded identity
    # has degree18. The other factor degrees give22+18+62+7+2+46=157.
    metrics['proved_factor_degrees']={'N0':22,'N1':18,'Na':62,'Nk':7,'Nt':2,'Ns':46}
    metrics['proved_exact_degree']=157
    dump(OUT/'polynomial.json',p)
    comparisons=[]
    for b,kind in [(55,'old55'),(53,'old53')]:
        vals,_,_=tuple_values(b,coefficients(decode_tiles(),False),kind)
        comparisons.append({'radix_bits':b,'raw_bytes':sum((v.bit_length()+7)//8 for v in vals.values()),'bits':{n:v.bit_length() for n,v in vals.items()}})
    report={'repository':'VladimirReshetnikov/ProveIt','commit':'55d1f72aedebf892e446c90d35fa1ae37689b0f2','radix_bits':49,'d':49*L,'phi_slots':3297,'phi_nonzero':sum(x!=0 for x in c),'phi_sha256':sha(json.dumps(c,separators=(',',':')).encode()),'independent_old_K_recovery':old,'binding':binding,'raw_bytes':sum(x['raw_bytes'] for x in binding.values()),'gzip_bytes':sum(x['gzip_bytes'] for x in binding.values()),'comparisons':comparisons,'metrics':metrics,'controller':cert,'masks':{'MC_population':values['MC'].bit_count(),'MF_native_population':mfn.bit_count(),'MC_mod4':values['MC']%4,'MF_native_mod8':mfn%8,'support_count':len(E)}}
    dump(OUT/'construction_report.json',report)
    print(json.dumps(report,indent=2,sort_keys=True))

if __name__=='__main__':main()
