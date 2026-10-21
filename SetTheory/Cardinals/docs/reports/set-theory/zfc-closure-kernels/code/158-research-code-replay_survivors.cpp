#define main search_main
#include "search_boot.cpp"
#undef main
struct Node{int left=-1,right=-1,ordinal=-1;};
vector<Node> trie(1);
vector<string> paths,ops;vector<int>args;
void read_source(string name){
 ifstream f(name);int n;f>>n;
 for(int i=0;i<n;i++){string p,op;int arg;f>>p>>op>>arg;paths.push_back(p);ops.push_back(op);args.push_back(arg);int j=0;
  for(char b:p){int c=b=='0'?trie[j].left:trie[j].right;if(c<0){c=trie.size();if(b=='0')trie[j].left=c;else trie[j].right=c;trie.push_back({});}j=c;}
  trie[j].ordinal=i;
 }
}
struct Frame{int ordinal=-1;vector<long>values;};
Frame any_frame(int h,const Tape&t){
 if(!clean(h,t))return{};
 int j=0,depth=0;
 while(trie[j].ordinal<0){j=t.read(h+depth)?trie[j].right:trie[j].left;depth++;if(j<0||depth>64)return{};}
 int header=h+52;while(header<=t.hi&&!t.read(header))header++;
 for(int p=h+depth;p<header;p++)if(t.read(p))return{};
 int p=header+1;vector<long>vals;
 while(p<=t.hi){if(t.read(p)||!t.read(p+1))return{};p++;int n=0;while(p<=t.hi&&t.read(p)){p++;n++;}vals.push_back(n-1);}
 if(vals.size()<10)return{};
 int phy[]={6,2,0,4,3,7,8,5,1};vector<long>result={header-h-64};for(int x:phy)result.push_back(vals[x]);result.insert(result.end(),vals.begin()+9,vals.end());
 return{trie[j].ordinal,result};
}
Result bootstrap_any(const Table&t,int start,int cap=1000000){
 Tape tape;int q=start,h=0;
 for(int k=0;k<=cap;k++){
  if(q==254)return {1,q,h,k,tape,{}};
  if(q==84&&any_frame(h,tape).ordinal>=0)return {0,q,h,k,tape,{}};
  if(k==cap)return {2,q,h,k,tape,{}};
  if(h<-OFFSET+2||h>=WIDTH-OFFSET-2)return {3,q,h,k,tape,{}};
  int b=tape.read(h),key=2*q+b;Action a=t[key];if(a.w<0)return {4,q,h,k,tape,{}};
  if(!b&&a.z==q&&((a.d==1&&h>=tape.hi)||(a.d==-1&&h<=tape.lo)))return {5,q,h,k,tape,{}};
  tape.write(h,a.w);h+=a.d;q=a.z;
 }
 throw runtime_error("unreachable");
}
#ifndef SKIP_REPLAY_MAIN
int main(int argc,char**argv){
 if(argc!=5&&argc!=6){cerr<<"table source survivors cap [witness_file]\n";return 2;}
 vector<int>states;auto t=load_table(argv[1],states);read_source(argv[2]);ifstream f(argv[3]);int cap=stoi(argv[4]);
 int q,b,w,d,z;long count=0;array<long,6>stats={};
 ofstream witnesses;if(argc==6)witnesses.open(argv[5]);
 auto began=chrono::steady_clock::now();
 while(f>>q>>b>>w>>d>>z){Table u=t;u[2*q+b]={w,d,z};
  for(int start:states){auto r=bootstrap_any(u,start,cap);stats[r.status]++;count++;
   if(witnesses){witnesses<<'['<<q<<','<<b<<','<<w<<','<<d<<','<<z<<','<<start<<','<<r.status<<','<<r.steps<<','<<r.q<<','<<r.h<<",[";bool first=true;for(int i=r.tape.lo;i<=r.tape.hi;i++)if(r.tape.read(i)){if(!first)witnesses<<',';witnesses<<i;first=false;}witnesses<<"]]\n";}
   if(r.status==0){auto frame=any_frame(r.h,r.tape);cout<<"{\"row\":["<<q<<','<<b<<"],\"action\":["<<w<<','<<d<<','<<z<<"],\"start\":"<<start<<",\"steps\":"<<r.steps<<",\"head\":"<<r.h<<",\"ordinal\":"<<frame.ordinal<<",\"pc\":\""<<paths[frame.ordinal]<<"\",\"gap_registers_spares\":";dump_array(frame.values);cout<<",\"support\":";dump_support(r.tape);cout<<"}\n"<<flush;}
  }
 }
 cerr<<"starts tested "<<count<<" status_census ";for(int i=0;i<6;i++)cerr<<i<<':'<<stats[i]<<' ';cerr<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<'\n';
 return 0;
}
#endif
