"""Small shared parsers and exact identities for the K219 release."""
from pathlib import Path
import hashlib,json
BASE_ARCHIVE_SHA='04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b'
BASE_TABLE_SHA='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
BASE_SOURCE_SHA='0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
TABLE_SHA='142cb09f13f336cf23330f959d5e78e4249c47a3d8f728efed7c61cc38825a11'
SOURCE_SHA='e2e41a573aba9f6a763bca387900fd383a737822776b48e6a853db1714bb9adf'
CANONICAL_SHA='cce85a9adaf104ee4cbddd927a6bbb1b5b3fdf06fffb4a23b68faded169d36dc'
PHY=(6,2,0,4,3,7,8,5,1)

def require(condition,message):
    if not condition:raise ValueError(message)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def sha_file(path):return sha(Path(path).read_bytes())
def dump(path,value):Path(path).write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
def parse_table(raw,start=0,halt=254):
    table={};starts=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):starts.append(int(line.split()[-1]))
        elif line and not line.startswith('#'):
            q,bit,w,d,z=line.split();q,bit,w,z=map(int,(q,bit,w,z))
            require((q,bit)not in table and bit in(0,1)and w in(0,1)and d in('L','R'),'Malformed transition')
            table[q,bit]=(w,1 if d=='R'else-1,z)
    states={q for q,bit in table}
    require(starts==[start]and start in states and halt not in states,'Start or terminal convention')
    require(set(table)=={(q,bit)for q in states for bit in(0,1)},'Incomplete transition table')
    require({z for w,d,z in table.values()}-states=={halt},'Unexpected terminal label')
    return table

def table_bytes(table,start=0):
    return ('#! start '+str(start)+'\n'+''.join(f'{q} {bit} {w} {"R"if d==1 else"L"} {z}\n'for(q,bit),(w,d,z)in sorted(table.items()))).encode('ascii')
