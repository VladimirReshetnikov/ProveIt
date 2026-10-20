#include <bits/stdc++.h>
using namespace std;
struct Row{int w,d,q;};struct Tape{array<uint64_t,64> b{};bool get(int h)const{h+=512;return (b[h>>6]>>(h&63))&1;}void put(int h,int w){h+=512;uint64_t m=1ull<<(h&63);if(w)b[h>>6]|=m;else b[h>>6]&=~m;}bool operator==(Tape const&o)const{return b==o.b;}};
struct Case{string pc,op;int arg;Tape in,out;int outhead;bool halt;};
Row T[512][2];Row M[2];vector<int>Q;vector<Case>cases;int PHY[]={6,2,0,4,3,7,8,5,1};
Tape frame(string pc,vector<int> r, vector<int>sp,int gap){Tape t;t.put(-1,1);t.put(64+gap,1);for(int i=0;i<(int)pc.size();i++)t.put(i,pc[i]-'0');vector<int>v(9);for(int i=0;i<9;i++)v[PHY[i]]=r[i];for(int x:sp)v.push_back(x);int p=65+gap;for(int x:v){p++;for(int j=0;j<x+1;j++)t.put(p++,1);}return t;}
pair<string,int> inc(string pc){for(int i=(int)pc.size()-1;i>=0;i--){if(pc[i]=='0'){pc[i]='1';return {pc,0};}pc[i]='0';}return {pc,1};}
string strip(string pc,char bit,int n){for(int i=(int)pc.size()-1;i>=0;i--)if(pc[i]==bit&&--n==0)return pc.substr(0,i);return "";}
Case makecase(string pc,string op,int arg,int val=0,int bg=0){vector<int>r(9,bg),sp{1,1};int gap=0;r[arg<0?0:arg]=val;Case c;c.pc=pc;c.op=op;c.arg=arg;c.in=frame(pc,r,sp,gap);int shift=0;c.halt=op=="CH";
if(op=="CI"){r[arg]++;sp.push_back(1);tie(pc,shift)=inc(pc);}else if(op=="CD"&&r[arg]){r[arg]--;gap++;tie(pc,shift)=inc(pc);}else if(op=="CD"||op=="CB")tie(pc,shift)=inc(strip(pc,'0',op=="CD"?1:arg));else if(op=="CC")pc=strip(pc,'1',arg);
c.out=frame(pc,r,sp,gap+shift);if(shift){Tape u;for(int i=-1;i<1000;i++)if(c.out.get(i))u.put(i-shift,1);c.out=u;}c.outhead=-shift;return c;}
bool dispatch(Tape const&t,int h){if(!t.get(h-1))return false;for(int i=-256;i<h-1;i++)if(t.get(i))return false;int p=h+52;while(p<1500&&!t.get(p))p++;if(p<h+64||p>=1500)return false;p++;int blocks=0;while(p<1500){if(t.get(p))return false;if(!t.get(p+1)){for(int j=p+2;j<1500;j++)if(t.get(j))return false;break;}p++;while(p<1500&&t.get(p))p++;blocks++;}return blocks>=10;}
// Normalization applies only to the removed state b; selected branch rows may come from either old state.
bool check(int a,int b,int c0,int c1,Case const&c){Tape t=c.in;int q=84,h=0;for(int tick=0;tick<30000;tick++){
if(tick){if(q==254)return c.halt;if(q==84&&dispatch(t,h))return !c.halt&&h==c.outhead&&t==c.out;}
if(h< -255||h>=1500)return false;int v=t.get(h);Row r=(q==a?M[v]:T[q][v]);t.put(h,r.w);h+=r.d;q=r.q==b?a:r.q;
}return false;}
int main(int argc,char**argv){ifstream tf(argv[1]);string line;while(getline(tf,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,v,w,z;char d;s>>q>>v>>w>>d>>z;T[q][v]={w,d=='R'?1:-1,z};if(v==0)Q.push_back(q);}
ifstream sf(argv[2]);string pc,op;int arg;while(sf>>pc>>op>>arg){cases.push_back(makecase(pc,op,arg,0));if(op=="CD")cases.push_back(makecase(pc,op,arg,1));}
vector<int>order; // Start with widely distributed source guards; all cases follow.
for(int i=0;i<100;i++){int j=(i*61)%cases.size();if(find(order.begin(),order.end(),j)==order.end())order.push_back(j);}for(int i=0;i<(int)cases.size();i++)if(find(order.begin(),order.end(),i)==order.end())order.push_back(i);
M[0]=T[84][0];M[1]=T[84][1];for(int i:order)if(!check(84,-1,84,84,cases[i])){cerr<<"BASEFAIL "<<i<<" "<<cases[i].pc<<"\n";return 2;}cerr<<"BASEPASS "<<cases.size()<<"\n";
ofstream out(argv[3]);long long tests=0,passed=0;int pairs=0;auto beg=chrono::steady_clock::now();
for(int ii=0;ii<(int)Q.size();ii++)for(int jj=ii+1;jj<(int)Q.size();jj++){int a=Q[ii],b=Q[jj];if(b==0||b==84)continue;auto phi=[&](int q){return q==b?a:q;};int same=-1;for(int c=0;c<2;c++)if(T[a][c].w==T[b][c].w&&T[a][c].d==T[b][c].d&&phi(T[a][c].q)==phi(T[b][c].q))same=c;if(same<0)continue;int changed=1-same;pairs++;
for(int w=0;w<2;w++)for(int d:{-1,1})for(int z:Q){if(z==b)continue;M[same]=T[a][same];M[changed]={w,d,z};tests++;bool good=true;int n=0;for(int k:order){if(!check(a,b,a,a,cases[k])){good=false;break;}n++;}
if(good){passed++;cout<<"FOUND "<<a<<" "<<b<<" "<<changed<<" "<<w<<" "<<d<<" "<<z<<"\n";out<<a<<" "<<b<<" "<<changed<<" "<<w<<" "<<d<<" "<<z<<"\n";out.flush();}
}if(pairs%50==0)cerr<<"PROGRESS "<<pairs<<" "<<tests<<" "<<passed<<" "<<chrono::duration<double>(chrono::steady_clock::now()-beg).count()<<"\n";}
cerr<<"DONE "<<tests<<" "<<passed<<"\n";}
