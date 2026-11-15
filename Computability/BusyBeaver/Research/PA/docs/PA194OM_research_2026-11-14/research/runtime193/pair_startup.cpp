#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;}; struct E{int q,b;A a;};struct Node{int ch[2]={-1,-1};int pc=-1;};
static A base[3000][2],T[3000][2];static bool ex[3000];static unsigned char tape[65536];
int main(int argc,char**argv){
 if(argc<4){cerr<<"table edits paths [bound=200000] [max_edits=2]\n";return 2;}
 int bound=argc>4?stoi(argv[4]):200000;int maxedits=argc>5?stoi(argv[5]):2;
 vector<int> qs;ifstream tf(argv[1]);int q,b,w,n;char d;
 while(tf>>q>>b>>w>>d>>n){if(!ex[q])qs.push_back(q);ex[q]=1;base[q][b]={w,d=='R'?1:-1,n};T[q][b]=base[q][b];}
 vector<E> edits={{-1,0,{0,0,0}}};ifstream ef(argv[2]);while(ef>>q>>b>>w>>d>>n)edits.push_back({q,b,{w,d=='R'?1:-1,n}});
 vector<Node> trie(1);ifstream pf(argv[3]);string path;int pc;
 while(pf>>pc>>path){int z=0;for(char c:path){int k=c-'0';if(trie[z].ch[k]<0){int to=trie.size();trie[z].ch[k]=to;trie.emplace_back();}z=trie[z].ch[k];}trie[z].pc=pc;}
 long long tables=0,sims=0,ticks=0,halts=0,rays=0,caps=0,hits=0;int maxones=0;auto starttime=chrono::steady_clock::now();
 auto process=[&](int i,int j){
  if(i&&j&&edits[i].q==edits[j].q&&edits[i].b==edits[j].b)return;
  if(i)T[edits[i].q][edits[i].b]=edits[i].a;if(j)T[edits[j].q][edits[j].b]=edits[j].a;tables++;
  int ray[3000]={};
  for(int qq:qs){int z=qq,di=0;bitset<3000>vis;while(z>=0&&z<3000&&ex[z]&&!vis[z]){vis[z]=1;A a=T[z][0];if(di&&a.d!=di){di=0;break;}di=a.d;z=a.n;}if(z>=0&&z<3000&&vis[z]&&di)ray[qq]=di;}
  // Every successful blank run has a first write of1; the earlier all-zero
  // tape path is immaterial up to translation. These starts cover all starts.
  for(int stq:qs){if(T[stq][0].w!=1)continue;sims++;memset(tape,0,sizeof tape);int st=0,q=stq,h=32768,lo=32768,hi=32767,cnt=0;
   for(;st<bound;st++){
    if(q==254){halts++;break;}
    if(q==84&&cnt>=12&&lo==h-1){
     int z=0,pp=h;bool valid=true;while(trie[z].pc<0){if(pp>hi+1||pp-h>60){valid=false;break;}int to=trie[z].ch[tape[pp++]];if(to<0){valid=false;break;}z=to;}
     if(valid){int sourcepc=trie[z].pc;while(pp<=hi&&!tape[pp])pp++;if(pp<=hi&&pp>=h+48){int header=pp;vector<int>vals;pp++;
       while(pp<=hi&&valid){if(tape[pp]||pp+1>hi||!tape[pp+1]){valid=false;break;}int len=0;pp++;while(pp<=hi&&tape[pp]){pp++;len++;}vals.push_back(len-1);}
       if(valid&&vals.size()>=10){hits++;cout<<"{\"i\":"<<i<<",\"j\":"<<j<<",\"start\":"<<stq<<",\"steps\":"<<st<<",\"head\":"<<h-32768<<",\"site\":"<<sourcepc<<",\"gap\":"<<header-h-48<<",\"values\":[";for(size_t v=0;v<vals.size();v++){if(v)cout<<',';cout<<vals[v];}cout<<"],\"ones\":[";bool sep=false;for(int p=lo;p<=hi;p++)if(tape[p]){if(sep)cout<<',';sep=true;cout<<p-32768;}cout<<"]}"<<endl;break;}
      }}
    }
    if(abs(h-32768)>20000||cnt>20000){caps++;break;}
    int bit=tape[h];if(!bit&&ray[q]&&(!cnt||(ray[q]==1&&h>hi)||(ray[q]==-1&&h<lo))){rays++;break;}
    A a=T[q][bit];tape[h]=a.w;if(a.w!=bit){cnt+=a.w?1:-1;if(a.w){lo=min(lo,h);hi=max(hi,h);}else if(cnt==0){lo=h;hi=h-1;}else{if(lo==h)while(lo<hi&&!tape[lo])lo++;if(hi==h)while(hi>lo&&!tape[hi])hi--;}}maxones=max(maxones,cnt);h+=a.d;q=a.n;ticks++;
   }if(st==bound)caps++;
  }
  if(i)T[edits[i].q][edits[i].b]=base[edits[i].q][edits[i].b];if(j)T[edits[j].q][edits[j].b]=base[edits[j].q][edits[j].b];
 };
 for(int i=0;i<(int)edits.size();i++){
  process(0,i);
  if(maxedits>=2)for(int j=i+1;j<(int)edits.size();j++)process(i,j);
  if(i%10==0)cerr<<"PROGRESS i "<<i<<" tables "<<tables<<" sims "<<sims<<" ticks "<<ticks<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-starttime).count()<<'\n';
 }
 cerr<<"DONE tables "<<tables<<" sims "<<sims<<" ticks "<<ticks<<" halts "<<halts<<" rays "<<rays<<" caps "<<caps<<" hits "<<hits<<" maxones "<<maxones<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-starttime).count()<<'\n';
}
