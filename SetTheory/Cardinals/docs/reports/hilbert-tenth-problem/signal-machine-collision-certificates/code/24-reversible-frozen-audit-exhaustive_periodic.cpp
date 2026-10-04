// Independently authored exhaustive 64-periodic bit implementation.
// Only this file is compiled. No author/repository executable is used.
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using U=std::uint64_t;
struct Row{U window,e0,e1,delta;};
U bit(int x){return U(1)<<(x&63);}
U mask(std::initializer_list<int> xs){U m=0;for(int x:xs)m|=bit(x);return m;}
U interval(int a,int b){U m=0;for(int x=a;x<=b;x++)m|=bit(x);return m;}
U rot(U x,int k){k&=63;return k ? (x<<k)|(x>>(64-k)) : x;}
Row row(int lo,int hi,std::initializer_list<int> a,std::initializer_list<int>b){U u=mask(a),v=mask(b);return{interval(lo,hi),u,v,u^v};}
using Block=std::array<Row,3>;using Keys=std::array<U,3>;
const Block A={row(-4,6,{0,1},{0,2}),row(-4,8,{0,4},{0,3}),row(-5,8,{0,1,6},{-1,2,7})};
const Block B={row(-4,6,{0,2},{1,2}),row(-5,7,{0,3},{-1,3}),row(-5,8,{-5,0,3},{-5,0,1})};
void check(bool x,const char* message){if(!x){std::cerr<<message<<'\n';std::exit(1);}}
Keys raw(U s,const Block&b){Keys out{};for(int j=0;j<3;j++)for(int x=0;x<64;x++){U local=rot(s,64-x)&b[j].window;if(local==b[j].e0||local==b[j].e1)out[j]|=bit(x);}return out;}
struct Status{Keys isolated{},prospective{},selected{};};
Status status(U s,const Block&b,const Keys&ks){Status out{};for(int j=0;j<3;j++){U k=ks[j];while(k){int x=__builtin_ctzll(k);k&=k-1;U neighborhood=rot(interval(-30,30),x);int total=0;for(U bits:ks)total+=__builtin_popcountll(bits&neighborhood);bool iso=total==1;bool pro=raw(s^rot(b[j].delta,x),b)==ks;if(iso)out.isolated[j]|=bit(x);if(pro)out.prospective[j]|=bit(x);if(iso&&pro)out.selected[j]|=bit(x);}}return out;}
U apply(U s,const Block&b,const Keys&selection){for(int j=0;j<3;j++){U k=selection[j];while(k){int x=__builtin_ctzll(k);k&=k-1;s^=rot(b[j].delta,x);}}return s;}
std::uint64_t changed=0,rejected=0,multiple=0,calls=0;
U step(U s,const Block&b,bool verify){Keys ks=raw(s,b);Status ss=status(s,b,ks);U out=apply(s,b,ss.selected);if(verify){Keys kt=raw(out,b);check(ks==kt,"raw keys changed");Status st=status(out,b,kt);check(ss.isolated==st.isolated&&ss.prospective==st.prospective&&ss.selected==st.selected,"status drift");check(apply(out,b,st.selected)==s,"not involution");check(__builtin_popcountll(s)==__builtin_popcountll(out),"mass changed");int n=0;bool rej=false;for(int j=0;j<3;j++){n+=__builtin_popcountll(ss.selected[j]);rej|=bool(ss.isolated[j]&~ss.prospective[j]);}changed+=(s!=out);multiple+=(n>1);rejected+=rej;calls++;}return out;}
U f(U s){return step(step(s,A,false),B,false);}U inv(U s){return step(step(s,B,false),A,false);}
int main(){for(U word=0;word<(U(1)<<18);word++){U s=word<<23;step(s,A,true);step(s,B,true);check(inv(f(s))==s,"left inverse fails");check(f(inv(s))==s,"right inverse fails");}
// Explicitly spaced islands give two selected anchors in a 64-periodic word.
for(int j=0;j<3;j++)for(int k=0;k<3;k++)for(int a=0;a<2;a++)for(int b=0;b<2;b++)for(int g=29;g<=35;g++){U s=(a?A[j].e1:A[j].e0)|rot(b?A[k].e1:A[k].e0,g);step(s,A,true);step(s,B,true);check(inv(f(s))==s,"island inverse fails");}
check(changed&&rejected&&multiple,"vacuous tests");std::cout<<"{\n  \"all_checks_passed\": true,\n  \"period\": 64,\n  \"exhaustive_binary_words\": 262144,\n  \"word_width\": 18,\n  \"additional_island_words\": 252,\n  \"verified_blocks\": "<<calls<<",\n  \"changed_blocks\": "<<changed<<",\n  \"isolated_rejection_blocks\": "<<rejected<<",\n  \"multiple_selection_blocks\": "<<multiple<<"\n}\n";}
