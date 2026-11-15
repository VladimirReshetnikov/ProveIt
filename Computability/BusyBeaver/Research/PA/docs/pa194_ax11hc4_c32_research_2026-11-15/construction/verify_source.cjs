#!/usr/bin/env node
/* Port of the symbolic source-frame checker in ProveIt commit 2ca99e3d23a5397aae4c786f4da7dfe1cca87f85, PA/docs/pa194_conpa_2026-11-13/construction/symbolic_runtime.py. The inherited arithmetic-block lemmas are assumed unchanged, not inferred from bounded testing. Original authorship and licenses are retained under licenses/. */

function makeVerifier(table, physical) {
  const BIT=[['b',0],['b',1]], PLAIN=['x','none',-1];
  const SK=[51,36,25,48,32,33,22,55,60], sk=new Map(SK.map((q,r)=>[q,r]));
  const frame=(p,extra=0,effect=PLAIN)=>[84,false,[BIT[1]],[...Array.from(p,b=>BIT[+b]),['r',0,1,48+extra-p.length],BIT[1],effect]];
  function norm(seg,left=false){const out=[];for(let x of seg){if(x[0]==='b')x=['r',x[1],0,1];if(x[0]==='r'&&x[2]===0&&x[3]===0)continue;const y=out.at(-1);if(y&&x[0]==='r'&&y[0]==='r'&&x[1]===y[1])out[out.length-1]=['r',x[1],x[2]+y[2],x[3]+y[3]];else out.push(x);}const y=out.at(-1);if(left&&y&&y[0]==='r'&&y[1]===0)out.pop();return out;}
  const canonical=([q,onl,l,r])=>[q,onl,norm(l,true),norm(r)];
  const eq=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
  const matches=(s,t)=>s[0]===t[0]&&s[1]===t[1]&&eq(norm(s[2],true),t[2])&&eq(norm(s[3]),t[3]);
  function oracle(q,br,x){const kind=x[1];let r=x[2];if(kind==='none'&&sk.has(q)){r=sk.get(q);return[r===0?1:3,['x','mark',r],false];}if(kind==='mark'&&r<9){if(q===64)return[40,['x','inc',r],false];if(q===0&&br!==null&&br[0]===r)return br[1]?[97,PLAIN,false]:[40,['x','dec',r],true];}return null;}
  function step(br,s){
    const[q,onl,l,r]=s;
    if(onl){
      if(l.length===0)return[[q,false,[],[BIT[0],...r]],false];
      const x=l[0],tail=l.slice(1);
      if(x[0]==='b')return[[q,false,tail,[x,...r]],false];
      if(x[0]==='r'){
        const[,b,a,c]=x,act=table.get(q+','+b);
        if(act&&act[1]===-1&&act[2]===q)return[[q,true,tail,[['r',act[0],a,c],...r]],false];
        if(c>0)return[[q,true,[BIT[b],['r',b,a,c-1],...tail],r],false];
        if(a===0)return[[q,true,tail,r],false];
      }
      return null;
    }
    if(r.length===0)return null;
    const x=r[0],tail=r.slice(1);
    if(x[0]==='b'){
      const act=table.get(q+','+x[1]);if(!act)return null;
      const[w,d,n]=act;
      return[d===1?[n,false,[BIT[w],...l],tail]:[n,true,l,[BIT[w],...tail]],true];
    }
    if(x[0]==='r'){
      const[,b,a,c]=x,act=table.get(q+','+b);
      if(act&&act[1]===1&&act[2]===q)return[[q,false,[['r',act[0],a,c],...l],tail],false];
      if(c>0)return[[q,false,l,[BIT[b],['r',b,a,c-1],...tail]],false];
      if(a===0)return[[q,false,l,tail],false];
      return null;
    }
    if(tail.length)return null;
    const oc=oracle(q,br,x);
    if(oc!==null){const[n,x2,extra]=oc;return[[n,true,extra?[BIT[1],...l]:l,[x2]],false];}
    const act=table.get(q+',0');
    if(act&&act[0]===0&&act[1]===-1)return[[act[2],true,l,r],true];
    return null;
  }
  function compile(sites){
    const index=new Map(sites.map((s,i)=>[s[0],i]));
    function locate(p){if(index.has(p))return index.get(p);for(let i=0;i<sites.length;i++){const q=sites[i][0];if(q.startsWith(p)||(p.startsWith(q)&&!p.slice(q.length).includes('1')))return i;}throw Error('missing path '+p);}
    function after(p){for(let i=p.length-1;i>=0;i--)if(p[i]==='0')return locate(p.slice(0,i)+'1');throw Error('source exit');}
    function cut(p,bit,k){for(let i=p.length-1;i>=0;i--)if(p[i]===bit){if(--k===0)return p.slice(0,i);}throw Error('source cut');}
    const instructions=[],contracts=[];
    for(let i=0;i<sites.length;i++){
      const[p,op,arg]=sites[i];let ins;
      if(op==='inc')ins=['inc',arg,after(p)];
      else if(op==='dec')ins=['dec',arg,after(cut(p,'0',1)),after(p)];
      else if(op==='breakTo')ins=['jump',after(cut(p,'0',arg))];
      else if(op==='continueTo')ins=['jump',locate(cut(p,'1',arg))];
      else if(op==='halt')ins=['halt'];else throw Error('bad opcode');
      instructions.push(ins);const st=frame(p);
      if(ins[0]==='inc')contracts.push([i,null,st,canonical(frame(sites[ins[2]][0],0,['x','inc',physical[arg]]))]);
      else if(ins[0]==='dec'){
        contracts.push([i,[physical[arg],true],st,canonical(frame(sites[ins[2]][0]))]);
        contracts.push([i,[physical[arg],false],st,canonical(frame(sites[ins[3]][0],1,['x','dec',physical[arg]]))]);
      } else if(ins[0]==='jump')contracts.push([i,null,st,canonical(frame(sites[ins[1]][0]))]);
      else contracts.push([i,null,st,null]);
    }
    return {instructions,contracts};
  }
  function run(contract,fuel=1024){
    const[site,br,initial,target]=contract;let s=initial,moved=false;
    for(let k=0;k<fuel;k++){
      if(moved&&(target===null?s[0]===254:matches(s,target)))return k;
      const next=step(br,s);if(next===null)return null;
      [s]=next;moved ||= next[1];
    }
    return null;
  }
  function validate(sites){
    const{instructions,contracts}=compile(sites);let total=0,maximum=0;
    for(const contract of contracts){const k=run(contract);if(k===null)throw Error('contract failed at site '+contract[0]+' branch '+JSON.stringify(contract[1]));total+=k;maximum=Math.max(maximum,k);}
    return{instructions,outcomes:contracts.length,total_symbolic_iterations:total,max_symbolic_iterations:maximum};
  }
  return{compile,validate,run};
}

const fs=require('node:fs'), path=require('node:path'), crypto=require('node:crypto');
const root=__dirname;
const native=fs.readFileSync(process.argv[2]||path.join(root,'cycle32','pa194_cycle32.native.tm'),'utf8');
const grammar=JSON.parse(fs.readFileSync(path.join(root,'source','source_grammar.json'),'utf8'));
const sha=s=>crypto.createHash('sha256').update(s,'utf8').digest('hex');
if(sha(native)!=='7a83339f95624c0d9b3935f081f226b17461dac6c4660e03a400ce04be8e0a9e')throw Error('native table hash');
if(sha(JSON.stringify(grammar))!=='70456686f1a4f3f720be00d2c4a0012f59259b0dc6e2c3c4d675e38dcd089c03')throw Error('grammar hash');
const sites=[],ops={i:'inc',d:'dec',b:'breakTo',c:'continueTo',h:'halt'};
function expand(id,p){const e=grammar.entries[id];if(typeof e==='string')sites.push([p,ops[e[0]],e.length>1?+e.slice(1):null]);else{expand(e[0],p+'0');expand(e[1],p+'1');}}
expand(grammar.root,'');
if(sites.length!==3673)throw Error('source site count');
const table=new Map(native.trim().split('\n').map(l=>{const[q,b,w,d,n]=l.split(' ');return[q+','+b,[+w,d==='R'?1:-1,+n]]}));
const result=makeVerifier(table,[6,4,0,3,2,8,7,5,1]).validate(sites);
const instructionHash=sha(JSON.stringify(result.instructions)+'\n');
if(instructionHash!=='78e7ceb6ada6c162c6a72dea0efc3a0fd9e7c67b2a9015823569f077f3e9d90d')throw Error('pinned instruction graph');
delete result.instructions;
if(result.outcomes!==4780||result.total_symbolic_iterations!==1479348||result.max_symbolic_iterations!==497)throw Error('unexpected contract receipt');
const receipt={status:'PASS',name:'PA194C32',...result,source_sites:3673,native_sha256:sha(native),compact_grammar_sha256:sha(JSON.stringify(grammar)),source_instructions_sha256:instructionHash,arithmetic_box_oracles:true,proof_assistant_kernel_checked:false,arithmetical_calibration_proved:false,scope:'Universal source-frame contracts under the unchanged generic arithmetic-block lemmas; not a completed iPRA consistency theorem.'};
fs.writeFileSync(path.join(root,'receipts','node_source.json'),JSON.stringify(receipt,null,2)+'\n');
console.log(JSON.stringify(receipt,null,2));
