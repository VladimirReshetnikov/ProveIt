#include <array>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <set>
#include <unordered_set>
#include <cstdint>
#include <algorithm>
using namespace std;
struct Row{int w,d,z;};array<array<Row,2>,1600>T;array<unordered_set<uint64_t>,1600>I;int R=20,N;uint64_t mask;const int OFFSET=1024,LEN=2048;int phy[9]={6,2,0,4,3,7,8,5,1};array<unsigned char,LEN> tape,goal;
string inc(string s,int &ov){ov=1;for(int k=(int)s.size()-1;k>=0;--k){if(s[k]=='0'){s[k]='1';ov=0;break;}s[k]='0';}return s;}
string cut(string s,char b,int n){for(int k=(int)s.size()-1;k>=0;--k)if(s[k]==b&&!--n)return s.substr(0,k);return "";}
void frame(array<unsigned char,LEN>&a,string pc,array<int,9>rs,vector<int>sp,int gap,int h){a.fill(0);a[OFFSET+h-1]=1;for(int j=0;j<(int)pc.size();++j)a[OFFSET+h+j]=pc[j]-'0';int pos=OFFSET+h+64+gap;a[pos++]=1;array<int,9>v;for(int j=0;j<9;++j)v[phy[j]]=rs[j];for(int x:v){++pos;for(int j=0;j<=x;++j)a[pos++]=1;}for(int x:sp){++pos;for(int j=0;j<=x;++j)a[pos++]=1;}}
void record_run(int q,int h,int haltq,int endh,int ticks=100000){uint64_t x=0;for(int k=0;k<N;++k)x|=uint64_t(tape[OFFSET+h-R+k])<<k;for(int k=0;k<ticks;++k){I[q].insert(x);auto r=T[q][tape[OFFSET+h]];tape[OFFSET+h]=r.w;uint64_t y=(x&~(1ULL<<R))|(uint64_t(r.w)<<R);if(r.d==1)x=(y>>1)|(uint64_t(tape[OFFSET+h+R+1])<<(N-1));else x=((y<<1)&mask)|tape[OFFSET+h-R-1];h+=r.d;q=r.z;if(q==254){if(haltq!=254)throw runtime_error("unexpected halt");return;}if(haltq==84&&q==84&&h==endh&&tape==goal)return;}if(haltq!=-1)throw runtime_error("no expected endpoint");}
int main(int argc,char**argv){if(argc>4)R=stoi(argv[4]);N=2*R+1;mask=(1ULL<<N)-1;ifstream in(argv[1]);string ln;while(getline(in,ln)){if(ln.empty()||ln[0]=='#')continue;istringstream s(ln);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;T[q][b]={w,d=='L'?-1:1,z};}ifstream sites(argv[2]);vector<tuple<string,string,int>>ss;string pc,op;int arg;while(sites>>pc>>op>>arg)ss.emplace_back(pc,op,arg);long long count=0;
for(int mode=0;mode<12;++mode){int ix=0;for(auto [pc,op,arg]:ss){for(int pos=0;pos<(op=="CD"?2:1);++pos){array<int,9>regs{};for(int i=0;i<9;++i)regs[i]= mode<3?mode:((i*17+ix*11+mode*13)%(mode<8?4:12));if(op=="CD")regs[arg]=pos?(mode<3?mode+1:regs[arg]+1):0;vector<int>spares=mode<3?vector<int>{mode}:vector<int>{mode%4,(mode+1)%3,mode%2};int gap=mode%3,ov=0,delta=0;frame(tape,pc,regs,spares,gap,0);auto rs=regs;auto sp=spares;string nxt;
if(op=="CI"){++rs[arg];sp.push_back(1);nxt=inc(pc,ov);}else if(op=="CD"&&pos){--rs[arg];delta=1;nxt=inc(pc,ov);}else if(op=="CD"||op=="CB")nxt=inc(cut(pc,'0',op=="CD"?1:arg),ov);else if(op=="CC")nxt=cut(pc,'1',arg);else nxt="";
frame(goal,nxt,rs,sp,gap+delta+ov,-ov);record_run(84,0,op=="CH"?254:84,-ov);++count;}++ix;}cerr<<"mode "<<mode<<" cases "<<count<<endl;}
tape.fill(0);record_run(0,0,-1,0,312617);ofstream out(argv[3]);long long patterns=0;for(int q=0;q<1600;++q){vector<uint64_t> xs(I[q].begin(),I[q].end());sort(xs.begin(),xs.end());for(auto x:xs){out<<q<<" "<<x<<"\n";++patterns;}}cerr<<"DONE patterns "<<patterns<<" cases "<<count<<endl;
}
