// Fresh research screen. Full-frame hits only; negative cutoffs prove nothing.
#include <bits/stdc++.h>
using namespace std;
struct Act{int w,d,n;};struct Edit{int q,b;Act a;};struct Seed{int pc;string path;int arbitrary;};
constexpr int WIDTH=50001,OFF=25000;
Act base[3000][2],row[3000][2];bool ex[3000];vector<int>qs;vector<Edit>es;vector<Seed>seeds;
int initial=74; int bound=200000,depth=4;uint64_t runs[6]{},ticks=0,limits=0,rays=0,halts=0,hits=0,cycles=0;unordered_set<uint64_t> seen;vector<int>ids;auto t0=chrono::steady_clock::now();
uint64_t key(vector<int> v){sort(v.begin(),v.end());uint64_t k=1;for(int i:v)k=k*512+(i+1);return k;}
bitset<6000> simulate(){static unsigned char tape[WIDTH];memset(tape,0,WIDTH);int h=OFF,q=initial,mi=OFF,ma=OFF,ones=0;bitset<6000>used;int raydir[3000]{};
 for(int s:qs){int r=s,d=0;bitset<3000>vis;while(ex[r]&&!vis[r]){vis[r]=1;auto a=row[r][0];if(d&&a.d!=d){d=0;break;}d=a.d;r=a.n;}if(d&&vis[r])raydir[s]=d;}
 runs[ids.size()]++;unordered_set<string> configurations;
 for(int st=0;st<=bound;st++){
  if(!ex[q]){halts++;return used;}
  if(st==bound||h<100||h>=WIDTH-100||ones>20000){limits++;return used;}
  if(st%64==0 && ones<=128 && ma-mi<=1024){string sig;sig.append(reinterpret_cast<char*>(&q),sizeof q);sig.append(reinterpret_cast<char*>(&h),sizeof h);for(int p=mi;p<=ma;p++)if(tape[p])sig.append(reinterpret_cast<char*>(&p),sizeof p);if(!configurations.insert(sig).second){cycles++;return used;}}
  if(q==84&&ones>=13){while(mi<=ma&&!tape[mi])mi++;while(ma>=mi&&!tape[ma])ma--;if(mi==h-1)for(auto &s:seeds){bool ok=true;int p=h;for(char c:s.path){if(tape[p++]!=c-'0'){ok=false;break;}}if(!ok)continue;while(p<=ma&&!tape[p])p++;if(p<h+48||p>ma)continue;int hdr=p;vector<int>vs;
   while(p<ma){if(tape[++p]||!tape[++p]){ok=false;break;}int len=0;while(tape[p]){len++;p++;}vs.push_back(len-1);p--;}
   if(!ok||vs.size()<10)continue;hits++;cout<<"{\"edits\":[";for(int i=0;i<(int)ids.size();i++){if(i)cout<<',';cout<<ids[i];}cout<<"],\"start\":"<<initial<<",\"steps\":"<<st<<",\"pc\":"<<s.pc<<",\"head\":"<<h-OFF<<",\"gap\":"<<hdr-h-48<<",\"values\":[";for(int i=0;i<(int)vs.size();i++){if(i)cout<<',';cout<<vs[i];}cout<<"],\"ones\":[";bool first=true;for(int x=mi;x<=ma;x++)if(tape[x]){if(!first)cout<<',';first=false;cout<<x-OFF;}cout<<"]}"<<endl;return used;
  }}
  int b=tape[h];used[2*q+b]=1;auto a=row[q][b];int rd=raydir[q];if(!b&&rd&&((rd==1&&h>ma)||(rd==-1&&h<mi)||!ones)){bitset<3000>rv;int r=q;while(ex[r]&&!rv[r]){rv[r]=1;used[2*r]=1;r=row[r][0].n;}rays++;return used;}if(a.w!=b){ones+=a.w-b;tape[h]=a.w;if(a.w){mi=min(mi,h);ma=max(ma,h);}}h+=a.d;q=a.n;ticks++;
 }
 return used;
}
void dfs(){if(!seen.insert(key(ids)).second)return;auto used=simulate();if(ids.size()==depth)return;for(int i=0;i<(int)es.size();i++){auto e=es[i];if(!used[2*e.q+e.b])continue;bool conflict=false;for(int j:ids)if(es[j].q==e.q&&es[j].b==e.b)conflict=true;if(conflict)continue;row[e.q][e.b]=e.a;ids.push_back(i);dfs();ids.pop_back();row[e.q][e.b]=base[e.q][e.b];}
 if(ids.size()<=1){cerr<<"PROGRESS ids";for(int i:ids)cerr<<' '<<i;cerr<<" runs";for(int i=0;i<=depth;i++)cerr<<' '<<runs[i];cerr<<" ticks "<<ticks<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<endl;}
}
int main(int argc,char**argv){if(argc<4)return 2;if(argc>4)depth=stoi(argv[4]);if(argc>5)bound=stoi(argv[5]);if(depth<0||depth>5||bound<1){cerr<<"Require 0<=depth<=5 and positive bound\n";return 2;}ifstream f(argv[1]);int q,b,w,n;char dir;while(f>>q>>b>>w>>dir>>n){if(!ex[q])qs.push_back(q);ex[q]=true;row[q][b]=base[q][b]={w,dir=='R'?1:-1,n};}ifstream ef(argv[2]);int id;Edit e;while(ef>>id>>e.q>>e.b>>e.a.w>>e.a.d>>e.a.n)es.push_back(e);ifstream sf(argv[3]);Seed s;while(sf>>s.pc>>s.path>>s.arbitrary)seeds.push_back(s);if(argc>6 && string(argv[6])=="all"){for(int start:qs){initial=start;seen.clear();dfs();}}else{if(argc>6)initial=stoi(argv[6]);dfs();}cerr<<"DONE runs";for(int i=0;i<=depth;i++)cerr<<' '<<runs[i];cerr<<" ticks "<<ticks<<" limits "<<limits<<" rays "<<rays<<" halts "<<halts<<" exact_cycles "<<cycles<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<endl;}
