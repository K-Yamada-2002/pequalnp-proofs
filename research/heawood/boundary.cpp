// Search every normalized circuit compatible with a listed first gate.
#include <algorithm>
#include <array>
#include <cstdint>
#include <chrono>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using Wire = std::uint64_t;
using Cover = std::array<std::uint64_t, 6>;
using State = std::array<Wire, 24>; // sorted wires, zero padding, then width and budget

struct Hash {
    std::size_t operator()(const State& s) const {
        std::size_t h = 0;
        for (auto x : s) h = h * 1000003 + x;
        return h;
    }
};

struct Projection {
    std::array<unsigned,22> zeros{};
    std::array<unsigned,7> credit{};
};

struct Search {
    int projections = 0;
    int credit_limit = 0;
    int positives, negatives;
    Wire target, negative_bits;
    std::vector<Wire> input_wires;
    // Replacing a gate by a wire that is at least as good on every boundary
    // assignment preserves the target for every monotone continuation.
    bool dominates(Wire replacement, Wire value) const {
        return !(value & target & ~replacement) && !(replacement & negative_bits & ~value);
    }
    Cover needed{};
    std::unordered_map<Wire, Cover> labels;
    std::unordered_set<State, Hash> rejected;
    std::uint64_t nodes = 0;
    std::chrono::steady_clock::time_point deadline = std::chrono::steady_clock::time_point::max();

    Cover coverage(Wire wire) {
        auto found = labels.find(wire);
        if (found != labels.end()) return found->second;
        Cover c{};
        for (int i=0; i<positives; ++i) if ((wire >> i) & 1U) {
            for (int j=0; j<negatives; ++j) if (!((wire >> (positives+j)) & 1U)) {
                int bit = i * negatives + j;
                c[bit/64] |= std::uint64_t(1) << (bit%64);
            }
        }
        labels.emplace(wire,c);
        return c;
    }

    bool visit(State wires, int n, int budget, const Projection& proj, const std::array<int,3>* first = nullptr) {
        ++nodes;
        if ((nodes & 65535) == 0 && std::chrono::steady_clock::now() >= deadline)
            throw std::runtime_error("time limit");
        if (std::find(wires.begin(),wires.begin()+n,target) != wires.begin()+n) return true;
        if (budget == 0 || n > budget+1) return false;
        State key=wires;
        if (!first) {
            std::sort(key.begin(),key.begin()+n);
            key[22]=n;
            key[23]=budget;
            if (rejected.count(key)) return false;
        }
        std::array<Cover,22> covers{};
        for (int i=0;i<n;++i) covers[i]=coverage(wires[i]);
        for (int i=0;i<n;++i) for (int j=i+1;j<n;++j) {
            if (first && (i!=(*first)[0] || j!=(*first)[1])) continue;
            State rest{};
            Projection carried=proj;
            int width=0;
            Cover unchanged{};
            for (int k=0;k<n;++k) if (k!=i && k!=j) {
                carried.zeros[width]=proj.zeros[k];
                rest[width++]=wires[k];
                for (int h=0;h<int(needed.size());++h) unchanged[h] |= covers[k][h];
            }
            for (int op : {0,1}) {
                if (first && op!=(*first)[2]) continue;
                Wire value = op ? wires[i]|wires[j] : wires[i]&wires[j];
                if (!(value & target) || (value & negative_bits)==negative_bits) continue;
                auto usable=[&](Wire old){ return dominates(old,value); };
                if (std::any_of(input_wires.begin(),input_wires.end(),usable) ||
                    std::any_of(wires.begin(),wires.begin()+n,usable)) continue;
                auto cover=coverage(value);
                for (int h=0;h<int(needed.size());++h) cover[h] |= unchanged[h];
                for (int save=0;save<4;++save) {
                    int next_width=width+1+(save&1)+(save>>1);
                    if (next_width>budget) continue;
                    bool ok=true;
                    for (int h=0;h<int(needed.size());++h) {
                        auto bits=cover[h];
                        if (save&1) bits |= covers[i][h];
                        if (save&2) bits |= covers[j][h];
                        if (bits!=needed[h]) { ok=false; break; }
                    }
                    if (!ok) continue;
                    Projection child=carried;
                    const unsigned a=proj.zeros[i], b=proj.zeros[j];
                    // Projection bits mark a zero wire when that point is deleted.
                    unsigned hit=a|b, zero=op ? (a&b) : (a|b);
                    bool feasible=true;
                    for (int h=0;h<projections;++h) {
                        const unsigned bit=1U<<h;
                        // Add the eliminated prefix gate and the new zero live wire.
                        // An operand being forgotten also leaves the live-zero count.
                        int gain=bool(hit&bit)+bool(zero&bit)
                            -(!(save&1) && (a&bit))-(!(save&2) && (b&bit));
                        child.credit[h]+=gain;
                        if (int(child.credit[h])>credit_limit) { feasible=false; break; }
                    }
                    if (!feasible) continue;
                    State next=rest;
                    int t=width;
                    child.zeros[t]=zero;
                    next[t++]=value;
                    if (save&1) { child.zeros[t]=a; next[t++]=wires[i]; }
                    if (save&2) { child.zeros[t]=b; next[t++]=wires[j]; }
                    if (visit(next,t,budget-1,child)) return true;
                }
            }
        }
        if (!first) {
            if (rejected.size()>=250000) rejected.clear();
            rejected.insert(key);
        }
        return false;
    }
};

int main(int argc, char** argv) {
    int n,e,budget,starts;
    if (!(std::cin>>n>>e>>budget>>starts) || n<2 || n>16 || budget>22) return 1;
    std::vector<int> samples;
    for (int k=0;k<e;++k) {
        int a,b; std::cin>>a>>b;
        samples.push_back((1<<a)|(1<<b));
    }
    std::vector<bool> positive(1<<n);
    for (int x=0;x<(1<<n);++x)
        for (int edge:samples) if ((x&edge)==edge) positive[x]=true;
    for (int x=0;x<(1<<n);++x) if (!positive[x]) {
        bool maximal=true;
        for (int i=0;i<n;++i)
            if (!(x&(1<<i)) && !positive[x|(1<<i)]) maximal=false;
        if (maximal) samples.push_back(x);
    }
    Search s;
    if (argc>=2) s.deadline = std::chrono::steady_clock::now() + std::chrono::seconds(std::stoi(argv[1]));
    s.positives=e;
    s.negatives=int(samples.size())-e;
    if (samples.size()>64 || e*s.negatives>384 || e>=64) throw std::runtime_error("boundary too large");
    s.target=(Wire(1)<<e)-1;
    s.negative_bits=(~Wire(0) >> (64-samples.size())) & ~s.target;
    s.needed=s.coverage(s.target);
    State initial{};
    for (int i=0;i<n;++i) for (unsigned k=0;k<samples.size();++k)
        if ((samples[k]>>i)&1) initial[i] |= Wire(1)<<k;
    s.input_wires.assign(initial.begin(),initial.begin()+n);
    Projection initial_projection{};
    if (argc==4) {
        s.projections=std::stoi(argv[2]);
        if (s.projections<1 || s.projections>7 || s.projections>n) return 1;
        s.credit_limit=budget-std::stoi(argv[3]);
        for (int i=0;i<s.projections;++i) {
            initial_projection.zeros[i]=1U<<i;
            initial_projection.credit[i]=1;
        }
    }
    for (int k=0;k<starts;++k) {
        std::array<int,3> first{};
        if (!(std::cin>>first[0]>>first[1]>>first[2])) return 1;
        bool found;
        try {
            found=s.visit(initial,n,budget,initial_projection,&first);
        } catch (const std::runtime_error& err) {
            std::cout<<"UNKNOWN at first gate "<<first[0]<<" "<<first[1]<<" "<<first[2]
                     <<", "<<s.nodes<<" visits: "<<err.what()<<std::endl;
            return 2;
        }
        if (found) {
            std::cout<<"SAT at first gate "<<first[0]<<" "<<first[1]<<" "<<first[2]<<std::endl;
            return 0;
        }
        std::cout<<"excluded "<<first[0]<<" "<<first[1]<<" "<<first[2]<<std::endl;
    }
    std::cout<<"UNSAT, "<<starts<<" first-gate classes, "<<s.nodes<<" visits\n";
}
