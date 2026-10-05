#!/usr/bin/env python3
"""Read-only reconciliation of ten original archives; never regenerate or extract data."""
from pathlib import Path
import argparse,hashlib,json,re,zipfile

def require(c,m):
    if not c:raise RuntimeError(m)
def sha(b):return hashlib.sha256(b).hexdigest()

def main():
    here=Path(__file__).resolve().parent
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--zip-dir',type=Path,default=Path('/workspace/scratch/416780682817/deliverables'))
    p.add_argument('--boundary-root',type=Path,default=Path('/workspace/shared/thue_morse_feedback_report'))
    p.add_argument('--allorders-data',type=Path,default=Path('/workspace/shared/thue_morse_all_orders/clean_replay/data'))
    p.add_argument('--output',type=Path,default=here/'recovery_map.json')
    a=p.parse_args()
    boundary={}
    for line in (here/'boundary_source_SHA256SUMS.txt').read_text().splitlines():
        h,rel=line.split(None,1);boundary[rel]=h
    chunks=json.loads((here/'all_orders_chunks_manifest.json').read_text())['parts']
    production=json.loads((here/'all_orders_production_manifest.json').read_text())['cases']
    expected={r['pressure_file']:r for r in production}
    records=[]; seen_boundary=set();seen_orders=set()
    for i in range(1,6):
        z=a.zip_dir/f'ProveIt_Thue_Morse_Boundary_Traces_{i}_of_5.zip'
        raw=z.read_bytes();members=[]
        with zipfile.ZipFile(z) as f:
            require(len(f.namelist())==len(set(f.namelist())),f'duplicate ZIP name: {z}')
            for name in f.namelist():
                prefix='ProveIt_Thue_Morse_First_Feedback_Boundary/'
                require(name.startswith(prefix),'unexpected archive prefix '+name)
                rel=name[len(prefix):]
                match=re.fullmatch(r'data/certificates/parity_m(\d{3})\.json\.trace\.gz',rel)
                require(match is not None,'unexpected trace member '+name)
                m=int(match.group(1));require(m not in seen_boundary,'duplicate boundary coverage')
                seen_boundary.add(m)
                content=f.read(name);source=(a.boundary_root/rel).read_bytes()
                require(content==source,'ZIP/source byte mismatch '+name)
                require(sha(content)==boundary[rel],'source-manifest mismatch '+name)
                members.append({'name':name,'m':m,'bytes':len(content),'sha256':sha(content),'source_relative_path':rel})
        records.append({'file':z.name,'bytes':len(raw),'sha256':sha(raw),'group':'boundary traces','extract_into':'Parent of ProveIt_Thue_Morse_First_Feedback_Boundary/ from the Boundary_Source archive','moment_coverage':sorted(r['m'] for r in members),'members':members})
    require(seen_boundary==set(range(2,70)),'boundary coverage is not exactly 2..69')
    for part in chunks:
        z=a.zip_dir/part['file'];raw=z.read_bytes()
        require(len(raw)==part['bytes'] and sha(raw)==part['sha256'],'chunk ZIP manifest mismatch '+z.name)
        members=[]
        with zipfile.ZipFile(z) as f:
            require(len(f.namelist())==len(set(f.namelist())),f'duplicate ZIP name: {z}')
            for name in f.namelist():
                require(name.startswith('data/'),'unexpected all-orders prefix '+name)
                short=name[len('data/'):];r=expected[short];m=r['m']
                require(m not in seen_orders,'duplicate interval coverage')
                seen_orders.add(m);content=f.read(name);source=(a.allorders_data/short).read_bytes()
                require(content==source,'ZIP/source byte mismatch '+name)
                require(len(content)==r['pressure_bytes'] and sha(content)==r['pressure_sha256'],'production manifest mismatch '+name)
                members.append({'name':name,'m':m,'bytes':len(content),'sha256':sha(content),'source_relative_path':short})
        require(sorted(r['m'] for r in members)==list(range(part['first_m'],part['last_m']+1)),'chunk coverage mismatch')
        records.append({'file':z.name,'bytes':len(raw),'sha256':sha(raw),'group':'all-orders interval JSON','extract_into':'Root of extracted ProveIt_Thue_Morse_All_Integer_Orders.zip, alongside its README.md; ZIP provides data/','moment_coverage':sorted(r['m'] for r in members),'members':members})
    require(seen_orders==set(range(2,112)),'all-orders interval coverage is not exactly 2..111')
    out={'status':'PASS','archives_checked':10,'entries_checked':sum(len(r['members']) for r in records),'boundary_traces':68,'all_orders_interval_files':110,'comparison':'Every member compared byte-for-byte with existing source data and against an existing source manifest; no data regenerated','scope':'The five all-orders ZIPs contain interval JSON files, not their optional generator traces. The five boundary ZIPs contain all 68 required compressed boundary traces.','archives':records}
    a.output.write_text(json.dumps(out,indent=2)+'\n')
    print('PASS: ten unchanged ZIPs; 178 byte-for-byte and source-manifest comparisons')

if __name__=='__main__':main()
