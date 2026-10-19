#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
struct Row{int w,d,q;};array<array<Row,2>,4096>T;
struct Case{bitset<512>a,z;int q,h;};vector<Case>cases;
int main(int argc,char**argv){ifstream tf(argv[1]);string s;getline(tf,s);int q,b,w,t;char d;while(tf>>q>>b>>w>>d>>t)T[q][b]={w,d=='R'?1:-1,t};
ifstream f(argv[2]);int n,k;while(f>>n){Case c;for(int i=0;i<n;i++){f>>k;c.a[k+128]=1;}f>>c.q>>c.h>>n;c.h+=128;for(int i=0;i<n;i++){f>>k;c.z[k+128]=1;}f>>n;for(int i=0;i<n;i++)f>>k;cases.push_back(c);}
long long steps=0;int good=0,bad=0,maxsteps=0,ic=0;for(auto&ex:cases){auto tape=ex.a;int q=96,h=128,visits=0,tick;bool ok=false;for(tick=0;tick<20000;tick++){steps++;if(h<0||h>=512)break;auto row=T[q][tape[h]];tape[h]=row.w;h+=row.d;q=row.q;if(q==254){ok=ex.q==254;break;}if(q==96){if(ex.q==96&&h==ex.h&&tape==ex.z){ok=true;break;}if(++visits>15)break;}}if(ok)good++;else{bad++;if(bad<=30)cout<<"FAIL case "<<ic<<" tick "<<tick+1<<" q "<<q<<" head "<<h-128<<endl;}maxsteps=max(maxsteps,tick+1);ic++;}
cout<<"DONE good="<<good<<" bad="<<bad<<" steps="<<steps<<" maximum_steps="<<maxsteps<<endl;return bad?1:0;}
