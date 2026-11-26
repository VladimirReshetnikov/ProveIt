#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

using Integer=std::int64_t;
constexpr int max_a=160;
constexpr Integer A=4LL*2401*2401;
std::array<std::vector<std::vector<int>>, max_a+1> middle;
bool separated(Integer D,Integer a,Integer b){
    return a==0 || (D>=16*a*a && 9*D*(b-a)*(b-a)>=16*a*a*b*b);
}
bool fast(Integer D) {
    int last=0, count=0;
    for(int a=1;a<=max_a && 3LL*a*a<=D;++a) {
        if(!separated(D,last,a)) continue;
        for(int b:middle[a][D%(4*a)]){
            Integer c=(D+b*b)/(4*a);
            if(c>=a && std::gcd(std::gcd(a,b),int(c%a))==1){
                ++count;last=a;break;
            }
        }
        if(count==5) return true;
    }
    return false;
}
int class_number(Integer D) {
    int h=0;
    for(Integer a=1;3*a*a<=D;++a){
        for(Integer b=0;b<=a;++b){
            if((D+b*b)%(4*a)) continue;
            Integer c=(D+b*b)/(4*a);
            if(c>=a && std::gcd(std::gcd(a,b),c)==1)
                h += (b==0 || a==b || a==c)?1:2;
        }
    }
    return h;
}
bool nonsplit(Integer D,int p) {
    if(D%(p*p)==0) return false;
    Integer v=(-D)%p;
    if(v<0)v+=p;
    if(!v) return true;
    for(int x=1;x<=(p-1)/2;++x) if(x*x%p==v) return false;
    return true;
}
std::array<Integer,5> ct{};
void process(Integer D) {
    if(D%4!=0 && D%4!=3)return;
    if(nonsplit(D,7) || nonsplit(D,13)){ct[0]++;return;}
    if(fast(D)){ct[1]++;return;}
    int h=class_number(D);
    if(h<6){ct[2]++;return;}
    for(int p:{19,31,37,43,61,67,73,79,97,103}){
        // p=1 mod 3, so zero is ordinary. Number of supersingular
        // residues S=(p-1)/12 if p=1 mod12, (p+5)/12 if p=7 mod12.
        int S=(p%12==1)?(p-1)/12:(p+5)/12;
        if(nonsplit(D,p) && h>4*S){ct[3]++;return;}
    }
    ++ct[4];std::cout << D << ' ' << h << '\n';
}
int main(){
    for(int a=1;a<=max_a;a++){
        middle[a].resize(4*a);
        for(int b=0;b<=a;b++) middle[a][(4*a-(b*b)%(4*a))%(4*a)].push_back(b);
    }
    for(Integer D=3;D<A;D++) process(D);
    assert(std::accumulate(ct.begin(), ct.end(), Integer(0)) == A/2 - 1);
    for(Integer s:ct)std::cerr<<s<<' ';
    std::cerr<<'\n';
}
