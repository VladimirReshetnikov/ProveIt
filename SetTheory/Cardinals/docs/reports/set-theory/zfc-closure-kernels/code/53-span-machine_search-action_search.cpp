// Independent C++ port of the source27 finite affine diagnostic rules.
// The four register-box summaries are explicit conditional contracts.
// Every positive recipe must be checked afresh by the original Python rules.
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <deque>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>

struct Action {int w=0,d=1,t=-1;};
using Table=std::array<std::array<Action,2>,255>;
struct Seg {
    int type,b,a,c;
    bool operator==(const Seg&o)const{return std::tie(type,b,a,c)==std::tie(o.type,o.b,o.a,o.c);}
};
using Side=std::deque<Seg>;
Seg bit(int b){return {0,b,0,1};}
Seg run(int b,int a,int c){return {1,b,a,c};}
Seg box(int kind=0,int reg=-1){return {2,kind,reg,0};}
Side canonical(const Side&s,bool left){
    Side out;
    for(auto x:s){
        if(x.type==2){out.push_back(x);continue;}
        if(x.type==0)x=run(x.b,0,1);
        assert(x.a>=0&&x.c>=0);
        if(x.a==0&&x.c==0)continue;
        if(!out.empty()&&out.back().type==1&&out.back().b==x.b){out.back().a+=x.a;out.back().c+=x.c;}
        else out.push_back(x);
    }
    if(left)while(!out.empty()&&out.back().type==1&&out.back().b==0)out.pop_back();
    return out;
}
struct Case {std::string pc,next;int reg,zero,halt,gap,effect,ereg,cost;Side targetL,targetR;};
struct Family {int dead;std::array<std::pair<int,int>,2> incoming;std::vector<int> affected;};
struct Result{int status,rules,literal;};
// status: 0 pass; -1/-2 pending incoming action; positives are diagnostic stops.
// 1 fuel, 2 unknown run, 3 unsupported box, 4 missing row, 5 malformed side.
Result check(const Table&t,const Case&c,const Family*family=nullptr,
             const std::array<int,2>&assigned={-1,-1},int fuel=1000){
    int q=96,literal=0;bool onleft=false;Side left{bit(1)},right;
    for(char b:c.pc)right.push_back(bit(b-'0'));
    right.push_back(run(0,1,40-int(c.pc.size())));right.push_back(bit(1));right.push_back(box());
    auto lookup=[&](int b,Action&out)->int{
        if(family)for(int i=0;i<2;++i)if(family->incoming[i]==std::pair<int,int>{q,b}&&assigned[i]<0)return -1-i;
        if(q<0||q>=255||t[q][b].t<0)return 4;
        out=t[q][b];return 0;
    };
    for(int step=0;step<fuel;++step){
        if(literal>0){
            if(c.halt&&q==254)return {0,step,literal};
            if(!c.halt&&!onleft&&q==96&&canonical(left,true)==c.targetL&&canonical(right,false)==c.targetR)return {0,step,literal};
        }
        if(onleft){
            if(left.empty()){right.push_front(bit(0));onleft=false;continue;}
            Seg x=left.front();
            if(x.type==0){left.pop_front();right.push_front(x);onleft=false;continue;}
            if(x.type!=1)return {5,step,literal};
            Action a;int failure=lookup(x.b,a);if(failure)return {failure,step,literal};
            if(a.d==-1&&a.t==q){left.pop_front();right.push_front(run(a.w,x.a,x.c));continue;}
            if(x.c>0){left.front().c--;left.push_front(bit(x.b));continue;}
            if(x.a==0){left.pop_front();continue;}
            return {2,step,literal};
        }
        if(right.empty())return {5,step,literal};
        Seg x=right.front();
        if(x.type==0){
            Action a;int failure=lookup(x.b,a);if(failure)return {failure,step,literal};
            q=a.t;++literal;
            if(a.d==1){left.push_front(bit(a.w));right.pop_front();}
            else{right.front()=bit(a.w);onleft=true;}
            continue;
        }
        if(x.type==1){
            Action a;int failure=lookup(x.b,a);if(failure)return {failure,step,literal};
            if(a.d==1&&a.t==q){left.push_front(run(a.w,x.a,x.c));right.pop_front();continue;}
            if(x.c>0){right.front().c--;right.push_front(bit(x.b));continue;}
            if(x.a==0){right.pop_front();continue;}
            return {2,step,literal};
        }
        if(x.type!=2||right.size()!=1)return {5,step,literal};
        const std::array<int,9> skip{60,44,31,56,38,40,28,64,69};
        bool applied=false;
        if(x.b==0)for(int r=0;r<9;++r)if(q==skip[r]){q=r==0?2:6;right.front()=box(1,r);onleft=true;applied=true;break;}
        if(applied)continue;
        if(x.b==1&&x.a>=0&&x.a<9){
            int r=x.a;
            if(q==73){q=48;right.front()=box(2,r);onleft=true;continue;}
            if(q==43&&c.reg==r){
                q=c.zero?3:(r==0?63:48);
                right.front()=c.zero?box():box(3,r);onleft=true;continue;
            }
        }
        Action a;int failure=lookup(0,a);if(failure)return {failure,step,literal};
        if(a.w!=0||a.d!=-1)return {3,step,literal};
        q=a.t;onleft=true;++literal;
    }
    return {1,fuel,literal};
}

std::vector<Case> readCases(const std::string&path){
    std::ifstream f(path);assert(f);std::vector<Case> out;Case c;
    while(f>>c.pc>>c.reg>>c.zero>>c.halt>>c.next>>c.gap>>c.effect>>c.ereg>>c.cost){
        if(c.next=="_")c.next="";c.targetL=canonical(Side{bit(1)},true);Side r;
        for(char b:c.next)r.push_back(bit(b-'0'));
        r.push_back(run(0,1,c.gap-int(c.next.size())));r.push_back(bit(1));r.push_back(box(c.effect,c.ereg));
        c.targetR=canonical(r,false);out.push_back(c);
    }
    assert(out.size()==8391);return out;
}
Table readTable(const std::string&path){
    std::ifstream f(path);assert(f);Table t;std::string line;int count=0;
    while(std::getline(f,line)){
        if(line.empty()||line[0]=='#')continue;
        std::istringstream s(line);int q,b,w,n;char d;s>>q>>b>>w>>d>>n;assert(s);
        t[q][b]={w,d=='R'?1:-1,n};++count;
    }
    assert(count==504);return t;
}
std::vector<Family> readFamily(const std::string&path){
    std::ifstream f(path);assert(f);std::vector<Family> out;Family x;int n;
    while(f>>x.dead>>x.incoming[0].first>>x.incoming[0].second>>x.incoming[1].first>>x.incoming[1].second>>n){
        x.affected.resize(n);for(int&i:x.affected)f>>i;assert(f);out.push_back(x);
    }
    assert(out.size()==46);return out;
}
std::vector<Action> actions(const Table&t,int dead,bool targetonly){
    std::vector<Action> out;
    for(int w=0;w<2;++w)for(int d:{1,-1})for(int q=0;q<255;++q)
        if(q!=dead&&(t[q][0].t>=0||q==254))out.push_back({w,d,q});
    assert(out.size()==1008);return out;
}
uint64_t weight(const std::array<int,2>&a,uint64_t count){return(a[0]<0?count:1)*(a[1]<0?count:1);}
struct Node{std::array<int,2> a;};
int main(int argc,char**argv){
    if(argc<3){std::cerr<<"Usage: action_search DATA_DIRECTORY OUTPUT_PREFIX [SECONDS=600] [FIRST_GROUP=0] [GROUP_COUNT=46] [TARGET_ONLY=0]\n";return 2;}
    std::string dir=argv[1],prefix=argv[2];double limit=argc>3?std::stod(argv[3]):600;
    int begin=argc>4?std::stoi(argv[4]):0,count=argc>5?std::stoi(argv[5]):46;
    bool targetonly=argc>6?std::stoi(argv[6]):false;
    auto t=readTable(dir+"/baseline.tm");auto cases=readCases(dir+"/cases.tsv");auto fam=readFamily(dir+"/family.tsv");
    for(size_t i=0;i<cases.size();++i){auto r=check(t,cases[i]);if(r.status||r.literal<=0){std::cerr<<"Baseline failure "<<i<<" "<<r.status<<"\n";return 3;}}
    std::cout<<"BASELINE 8391 PASS\n"<<std::flush;
    std::ofstream ledger(prefix+".ledger.tsv"),survivors(prefix+".survivors.tsv"),summary(prefix+".summary.tsv"),frontier(prefix+".frontier.tsv");
    assert(ledger&&survivors&&summary&&frontier);
    ledger<<"group\tdeleted\ta0\ta1\toutcome\tcase_or_needed\treason\tweight\n";
    summary<<"group\tdeleted\tplanned\tpruned\tremaining\tsurvivors\tnodes\tchecks\tseconds\n";
    auto start=std::chrono::steady_clock::now();uint64_t allchecks=0,allnodes=0,allpruned=0,allremain=0,allsurvivors=0;bool timed=false;
    for(int gi=begin;gi<std::min(46,begin+count);++gi){
        const auto&f=fam[gi];auto opts=actions(t,f.dead,false);
        std::array<std::vector<Action>,2> domains{opts,opts};
        if(targetonly)for(int j=0;j<2;++j){
            domains[j].clear();auto [q,b]=f.incoming[j];auto old=t[q][b];
            for(int v=0;v<254;++v)if(v!=f.dead&&t[v][0].t>=0)domains[j].push_back({old.w,old.d,v});
            assert(domains[j].size()==251);
        }
        uint64_t optioncount=domains[0].size(),planned=optioncount*optioncount,pruned=0,remaining=0,nodes=0,checks=0,good=0;
        std::vector<Node> stack{{{-1,-1}}};
        while(!stack.empty()){
            double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
            if(elapsed>=limit){timed=true;break;}
            auto n=stack.back();stack.pop_back();Table mutant=t;mutant[f.dead][0].t=mutant[f.dead][1].t=-1;
            for(int j=0;j<2;++j)if(n.a[j]>=0){auto[q,b]=f.incoming[j];mutant[q][b]=domains[j][n.a[j]];}
            int failed=-1,needed=-1,reason=0;
            for(int ci:f.affected){auto r=check(mutant,cases[ci],&f,n.a);++checks;
                if(r.status<0){needed=-r.status-1;break;}
                if(r.status){failed=ci;reason=r.status;break;}
            }
            if(failed<0&&needed<0)for(int ci=0;ci<int(cases.size());++ci){auto r=check(mutant,cases[ci],&f,n.a);++checks;
                if(r.status<0){needed=-r.status-1;break;}
                if(r.status){failed=ci;reason=r.status;break;}
            }
            if(failed<0&&needed<0)for(int j=0;j<2;++j)if(n.a[j]<0){needed=j;break;}
            ++nodes;
            ledger<<gi<<'\t'<<f.dead<<'\t'<<n.a[0]<<'\t'<<n.a[1]<<'\t';
            if(needed>=0){
                ledger<<"branch\t"<<needed<<"\t0\t0\n";
                for(int k=int(domains[needed].size())-1;k>=0;--k){auto child=n;child.a[needed]=k;stack.push_back(child);}
            }else if(failed>=0){uint64_t w=weight(n.a,optioncount);pruned+=w;ledger<<"prune\t"<<failed<<'\t'<<reason<<'\t'<<w<<'\n';}
            else{
                ++good;ledger<<"survivor\t-1\t0\t1\n";
                survivors<<gi<<' '<<f.dead;
                for(int j=0;j<2;++j){auto[q,b]=f.incoming[j];auto a=domains[j][n.a[j]];survivors<<' '<<q<<' '<<b<<' '<<a.w<<' '<<(a.d==1?'R':'L')<<' '<<a.t;}
                survivors<<'\n'<<std::flush;
                std::cout<<"SURVIVOR "<<f.dead<<' '<<n.a[0]<<' '<<n.a[1]<<'\n'<<std::flush;
            }
        }
        for(auto n:stack){uint64_t w=weight(n.a,optioncount);remaining+=w;frontier<<gi<<' '<<f.dead<<' '<<n.a[0]<<' '<<n.a[1]<<' '<<w<<'\n';}
        assert(planned==pruned+remaining+good);
        double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
        summary<<gi<<'\t'<<f.dead<<'\t'<<planned<<'\t'<<pruned<<'\t'<<remaining<<'\t'<<good<<'\t'<<nodes<<'\t'<<checks<<'\t'<<elapsed<<'\n'<<std::flush;
        std::cout<<"GROUP "<<gi<<" dead="<<f.dead<<" pruned="<<pruned<<" remaining="<<remaining<<" survivors="<<good<<" seconds="<<elapsed<<'\n'<<std::flush;
        allchecks+=checks;allnodes+=nodes;allpruned+=pruned;allremain+=remaining;allsurvivors+=good;
        if(timed){
            for(int gj=gi+1;gj<std::min(46,begin+count);++gj){frontier<<gj<<' '<<fam[gj].dead<<" -1 -1 "<<planned<<'\n';allremain+=planned;}
            break;
        }
    }
    std::cout<<"FINAL checks="<<allchecks<<" nodes="<<allnodes<<" pruned="<<allpruned<<" remaining="<<allremain<<" survivors="<<allsurvivors<<" partial="<<timed<<'\n';
}
