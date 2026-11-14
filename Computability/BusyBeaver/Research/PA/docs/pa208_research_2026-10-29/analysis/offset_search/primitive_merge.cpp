// Finite canonical-frame candidate screen. This is not a proof.
#include <array>
#include <vector>
#include <string>
#include <sstream>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <random>
#include <chrono>
using namespace std;
constexpr int LEN=768, ORIGIN=256, MAXQ=1024;
struct Row {int w,d,z;};
struct Case {array<unsigned char,LEN> tape,target; int head,prefix;bool halt;};
Row machine[MAXQ][2];
vector<Case> cases;
vector<int> affected[MAXQ];
vector<int> states;
int used[MAXQ];
bool protected_rows[MAXQ][2];
bool seen_rows[MAXQ][2];
int incoming_transform=0;
struct Trie {int next[2]={-1,-1};bool leaf=false;};
vector<Trie> trie(1);

void addprefix(string pc){
  int q=0;
  for(char c:pc){int b=c-'0';if(trie[q].next[b]<0){trie[q].next[b]=trie.size();trie.emplace_back();}q=trie[q].next[b];}
  trie[q].leaf=true;
}
int prefixlength(const array<unsigned char,LEN>&tape,int h){
  int q=0,k=0;
  while(!trie[q].leaf && h+k<LEN && k<150){q=trie[q].next[tape[h+k]];k++;if(q<0)return -1;}
  return trie[q].leaf?k:-1;
}

array<unsigned char,LEN> frame(string pc,vector<int>regs,vector<int>sp,int gap) {
    constexpr int phy[9]={6,2,0,4,3,7,8,5,1};
    vector<int> vals(9);for(int i=0;i<9;i++)vals[phy[i]]=regs[i];
    vals.insert(vals.end(),sp.begin(),sp.end());
    array<unsigned char,LEN>a{};a[ORIGIN-1]=a[ORIGIN+56+gap]=1;
    for(int i=0;i<(int)pc.size();i++)a[ORIGIN+i]=pc[i]=='1';
    int p=ORIGIN+57+gap;
    for(int v:vals){for(int j=1;j<=v+1;j++)a[p+j]=1;p+=v+2;}
    return a;
}
string strip(string pc,char b,int n) {
    for(int i=(int)pc.size()-1;i>=0;i--)if(pc[i]==b && --n==0)return pc.substr(0,i);
    return "";
}
pair<string,int> inc(string pc) {
    for(int i=(int)pc.size()-1;i>=0;i--){if(pc[i]=='0'){pc[i]='1';return {pc,0};}pc[i]='0';}
    return {pc,1};
}
void addcase(string pc,string op,int arg,vector<int>regs,vector<int>sp,int gap) {
    Case c;c.tape=frame(pc,regs,sp,gap);int shift=0,delta=0;c.halt=op=="CH";
    {
      auto tape=c.tape;int q=84,h=ORIGIN,steps=0;
      while(h!=ORIGIN+(int)pc.size()-1 && steps<10000){
        auto r=machine[q][tape[h]];tape[h]=r.w;h+=r.d;q=r.z;steps++;
      }
      if(steps==10000)throw runtime_error("Bad source prefix");
      c.prefix=steps;
    }
    if(op=="CI"){regs[arg]++;sp.push_back(1);tie(pc,shift)=inc(pc);}
    else if(op=="CD" && regs[arg]){regs[arg]--;delta=1;tie(pc,shift)=inc(pc);}
    else if(op=="CD"||op=="CB")tie(pc,shift)=inc(strip(pc,'0',op=="CD"?1:arg));
    else if(op=="CC")pc=strip(pc,'1',arg);
    c.target=frame(pc,regs,sp,gap+delta+shift);
    if(shift){for(int i=0;i<LEN-1;i++)c.target[i]=c.target[i+1];c.target[LEN-1]=0;}
    c.head=ORIGIN-shift;cases.push_back(c);
}
bool run(const Case&c,int drop,int keep,int limit,bool record=false,int cb=-1,Row repl={0,0,0}) {
    auto tape=c.tape;int q=84==drop?keep:84,h=ORIGIN;
    int dispatch=q,cutoff=-1;bool decoding=false;
    if(record)fill(begin(used),end(used),0);
    for(int step=0;step<=limit;step++) {
        if(step && ((c.halt && q==254)||(!c.halt && q==dispatch && h==c.head && tape==c.target)))return true;
        if(q==254||step==limit||h<0||h>=LEN)return false;
        int b=tape[h];Row r=q==keep && b==cb?repl:machine[q][b];
        if(record){
          used[q]=1;
          seen_rows[q][b]=true;
          if(q==84){int width=prefixlength(tape,h);decoding=width>0;cutoff=h+width-1;}
          if(h==cutoff)decoding=false;
          if(!decoding)protected_rows[q][b]=true;
        }
        if(r.z==drop){if(incoming_transform&1)r.w^=1;if(incoming_transform&2)r.d=-r.d;}
        tape[h]=r.w;h+=r.d;q=r.z==drop?keep:r.z;
    }
    return false;
}
int main(int argc,char**argv) {
    if(argc<4)throw runtime_error("Expected table, source TSV, and output file");
    ifstream input(argv[1]);string line;bool present[MAXQ]={};
    if(!input)throw runtime_error("Cannot open transition table");
    while(getline(input,line)){
        if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;
        machine[q][b]={w,d=='R'?1:-1,z};present[q]=true;
    }
    for(int q=0;q<MAXQ;q++)if(present[q])states.push_back(q);
    ifstream source(argv[2]);string pc,op;int arg;mt19937 rng(20261029);
    if(!source)throw runtime_error("Cannot open source TSV");
    while(source>>pc>>op>>arg){
        addprefix(pc);
        for(int a=0;a<2;a++){
            vector<int>regs(9,0),sp(a+1,0);int gap=a?3:0;
            if(a){for(int&v:regs)v=rng()%4;for(int&v:sp)v=rng()%4;}
            if(op=="CD"){regs[arg]=0;addcase(pc,op,arg,regs,sp,gap);regs[arg]=a+1;addcase(pc,op,arg,regs,sp,gap);}
            else addcase(pc,op,arg,regs,sp,gap);
        }
    }
    for(int i=0;i<(int)cases.size();i++){
        if(!run(cases[i],-1,-1,100000,true)){cerr<<"BASELINE FAIL "<<i<<endl;return 1;}
        for(int q:states)if(used[q])affected[q].push_back(i);
    }
    if(cases.empty())throw runtime_error("Empty source case set");
    cout<<"PREPARED "<<cases.size()<<" cases"<<endl;
    ofstream out(argv[3]);int mode=argc>4?stoi(argv[4]):0,limit=argc>5?stoi(argv[5]):10000;
    incoming_transform=argc>6?stoi(argv[6]):0;
    if(mode==-1 || mode==-2){
      array<unsigned char,LEN> tape{};int q=0,h=ORIGIN;
      for(int i=0;i<48140;i++){
        if(h<0||h>=LEN)throw runtime_error("Startup exceeded finite tape buffer");
        int b=tape[h];protected_rows[q][b]=true;seen_rows[q][b]=true;auto r=machine[q][b];
        tape[h]=r.w;h+=r.d;q=r.z;
      }
      int count=0;
      for(int q:states)for(int b=0;b<2;b++)if(mode==-1?protected_rows[q][b]:seen_rows[q][b]){out<<q<<' '<<b<<'\n';count++;}
      cout<<(mode==-1?"PROTECTED ":"SEEN ")<<count<<endl;return 0;
    }
    long long candidates=0,survivors=0;auto start=chrono::steady_clock::now();
    for(int drop:states){
        if(drop==0 || (incoming_transform && drop==84))continue;
        for(int keep:states){
            if(drop==keep)continue;
            if(mode==0){
                candidates++;bool ok=true;
                for(int i:affected[drop])if(!run(cases[i],drop,keep,limit)){ok=false;break;}
                if(ok){survivors++;out<<drop<<' '<<keep<<endl;cout<<"PASS "<<drop<<" -> "<<keep<<endl;}
            }else{
                vector<int> check=affected[drop];
                for(int i:affected[keep])if(!binary_search(affected[drop].begin(),affected[drop].end(),i))check.push_back(i);
                for(int cb=0;cb<2;cb++){
                  Row a=machine[drop][1-cb],b=machine[keep][1-cb];
                  if(a.z==drop)a.z=keep;if(b.z==drop)b.z=keep;
                  if(mode==1 && (a.w!=b.w || a.d!=b.d || a.z!=b.z))continue;
                  for(int z:states)if(z!=drop)for(int d:{-1,1})for(int w=0;w<2;w++){
                    candidates++;Row repl{w,d,z};bool ok=true;
                    for(int i:check)if(!run(cases[i],drop,keep,limit,false,cb,repl)){ok=false;break;}
                    if(ok){survivors++;out<<drop<<' '<<keep<<' '<<cb<<' '<<w<<' '<<d<<' '<<z<<endl;cout<<"PASS "<<drop<<" -> "<<keep<<" row "<<cb<<' '<<w<<' '<<d<<' '<<z<<endl;}
                  }
                }
            }
        }
        cout<<"PROGRESS "<<drop<<" candidates "<<candidates<<" survivors "<<survivors<<endl;
    }
    cout<<"DONE "<<candidates<<' '<<survivors<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
