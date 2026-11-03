"""Exact diagnostic matching for the proposed author-only tiling cut; no Lean invocation."""
import hashlib,re
from pathlib import Path
EXPECTED={'ArithmeticRunTrace':('7883f132853ab6718e324ab1028482919fd4fe6a33174c0004d19caff555beab','669a5e5153f13281a8a922f0987a37a60e15bb5cbd8bd0da0f96fcf6ba16f57c',9),'ArithmeticTilingTable':('f4f0781b71aa9c2e9cb589219488a6b695e60b2d6675cc11d869a0d333b6913d','e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',0),'ArithmeticTilingRows':('b9455daeb169cda962241e6d7508587f35295ac55977553ab81e7e880e9eaa71','75496c5439d3f1b7e1e5f5432c1472e77b19624ac411e400c7734b7a0cc6c12d',3),'ArithmeticTilingBand':('641a68ca0888cb4b7ac4f749703e6d4cb74367e92962234a65ee33a65dc467d0','25d200c3a5686a9164eaf702b7efd962fffcbdef860e603dd04bdafbf9df43ed',1),'ArithmeticTilingWord':('388375a1f9bc5487cb4f66a6bc70fdb05d9cb22b6d8b48181c4948113e6be5e6','efceaccdb32de6ab5be6a18abacb20c75a99456b55c7fea99cddb4af443577e0',9)}
HISTROOT='/tmp/ha87-frozen-full-e_jgyudl/tree/Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
def validate(name, source_sha, current_path, output, historical_log):
    if name not in EXPECTED:raise ValueError('unknown module')
    source_pin,log_pin,count=EXPECTED[name]
    if source_sha != source_pin:raise ValueError('source hash mismatch')
    if hashlib.sha256(historical_log.encode()).hexdigest()!=log_pin:raise ValueError('historical log hash mismatch')
    if not isinstance(current_path,str) or not current_path.startswith('/') or '\n' in current_path:raise ValueError('invalid current source path')
    if re.search(r'(?m)^.*error:|\bsorryAx\b|\bsorry\b',output):raise ValueError('error or sorry')
    if output.count('warning:')!=count or historical_log.count('warning:')!=count:raise ValueError('warning count mismatch')
    def normalize(text,path):
        return re.sub(r'(?m)^'+re.escape(path)+r'(?=:\d+:\d+: warning:)', '<SOURCE>', text)
    if normalize(output,current_path)!=normalize(historical_log,HISTROOT+name+'.lean'):raise ValueError('diagnostic text mismatch')
    return {'module':name,'warning_count':count,'source_sha256':source_pin,'historical_log_sha256':log_pin}
def validate_client(output):
    if re.search(r'(?m)^.*(?:warning:|error:)|\bsorryAx\b|\bsorry\b',output):raise ValueError('client diagnostics')
    pat=re.compile(r"^'CompactHaltWordViaSupplied\.halt_compact_word' depends on axioms:\s*\[([^\]]*)\]\s*$")
    m=pat.fullmatch(output)
    if not m:raise ValueError('client axiom report')
    vals=[x.strip() for x in m.group(1).split(',') if x.strip()]
    if not vals or len(vals)!=len(set(vals)) or not set(vals)<={'propext','Classical.choice','Quot.sound'}:raise ValueError('unpermitted axiom set')
    return vals
