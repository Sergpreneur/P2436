// P2436 exact all-pairs search, based on the parity-erased 61-bit field state.
// Author: Sergey Nefedov. C++17; no probabilistic collision decisions.
// Every exponent i=1..B is generated and its 60-bit key state(i)>>1 stored.
// Equal keys are exact potential trinomial solutions; all exponents are
// reconstructed by a second full LFSR pass and independently checked.
#include <algorithm>
#include <array>
#include <chrono>
#include <cinttypes>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace fs = std::filesystem;
using u64 = uint64_t;
constexpr u64 LIMIT = (1ULL << 31);
constexpr u64 MASK = (1ULL << 61) - 1;
constexpr u64 TAP = (1ULL << 45) | (1ULL << 32) | (1ULL << 2) | 1;
constexpr unsigned PARTITIONS = 256;
constexpr unsigned BUFFER_COUNT = 4096;
constexpr unsigned RADIX_BITS = 11;
constexpr unsigned RADIX = 1 << RADIX_BITS;
static_assert(sizeof(u64) == 8, "requires 64-bit uint64_t");

u64 mulX(u64 s) { return ((s << 1) & MASK) ^ (((s >> 60) & 1) ? TAP : 0); }
[[noreturn]] void fail(const std::string &s) { throw std::runtime_error(s); }
struct Pair {u64 a, b;};

std::string bucket_path(const fs::path &dir, unsigned id) {
  char b[40]; std::snprintf(b,sizeof(b),"bucket_%03u.bin",id);
  return (dir/b).string();
}

// Sort all 60-bit keys in a bucket by five EXACT stable radix passes.
void sort_exact(std::vector<u64> &v) {
  std::vector<u64> tmp(v.size());
  std::array<size_t,RADIX> counts{};
  for(unsigned shift=0;shift<55;shift+=RADIX_BITS) {
    counts.fill(0);
    for(u64 x : v) ++counts[(x >> shift) & (RADIX-1)];
    size_t off=0;
    for(size_t &count : counts) {const size_t c=count; count=off; off+=c;}
    for(u64 x : v) tmp[counts[(x >> shift)&(RADIX-1)]++] = x;
    v.swap(tmp);
  }
}

void generate(const fs::path &dir, u64 bound, std::array<u64,PARTITIONS> &counts, u64 &last_state) {
  std::array<FILE *,PARTITIONS> files{};
  std::vector<u64> buf(PARTITIONS*BUFFER_COUNT);
  std::array<unsigned,PARTITIONS> used{};
  for(unsigned p=0;p<PARTITIONS;++p) {
    files[p]=std::fopen(bucket_path(dir,p).c_str(),"wb");
    if(!files[p]) fail("cannot create bucket: disk quota or permission");
  }
  u64 state=1;
  for(u64 i=1;i<=bound;++i) {
    state=mulX(state);
    const u64 k=state >> 1;
    const unsigned p=(unsigned)(k>>52);
    if (p>=PARTITIONS) fail("out of range partition");
    u64 *base=buf.data()+((size_t)p*BUFFER_COUNT);
    base[used[p]++]=k;
    ++counts[p];
    if(used[p]==BUFFER_COUNT) {
      if(std::fwrite(base,sizeof(u64),BUFFER_COUNT,files[p])!=BUFFER_COUNT) fail("bucket write failed");
      used[p]=0;
    }
  }
  last_state=state;
  for(unsigned p=0;p<PARTITIONS;++p) {
    const u64 *base=buf.data()+((size_t)p*BUFFER_COUNT);
    if(used[p] && std::fwrite(base,sizeof(u64),used[p],files[p]) != used[p]) fail("final bucket write failed");
    if(std::fclose(files[p])) fail("bucket fclose failed");
    const u64 expected=counts[p]*sizeof(u64);
    if(fs::file_size(bucket_path(dir,p))!=expected) fail("invalid bucket byte size");
  }
}

void write_summary(const fs::path &dir, u64 bound, const std::array<u64,PARTITIONS>& counts,
                   const std::vector<u64>& collision_keys, const std::vector<Pair>& pairs,
                   u64 last_state, double seconds) {
  std::ofstream out(dir/"run_summary.json");
  if(!out) fail("cannot write summary");
  out << "{\n  \"polynomial_exponents\": [61, 45, 32, 2, 0],\n";
  out << "  \"inclusive_bound\": " << bound << ",\n";
  out << "  \"generated_count\": " << bound << ",\n";
  out << "  \"partition_count\": " << PARTITIONS << ",\n";
  out << "  \"last_state\": " << last_state << ",\n";
  out << "  \"collision_key_count\": " << collision_keys.size() << ",\n";
  out << "  \"collision_keys\": [";
  for(size_t i=0;i<collision_keys.size();++i) out << (i?", ":"") << collision_keys[i];
  out << "],\n  \"pairs\": [";
  for(size_t i=0;i<pairs.size();++i) out << (i?", ":"") << "[" << pairs[i].a << ", " << pairs[i].b << "]";
  out << "],\n  \"partition_counts\": [";
  for(size_t i=0;i<counts.size();++i) out << (i?", ":"") << counts[i];
  out << "],\n  \"elapsed_seconds\": " << seconds << "\n}\n";
  if(!out) fail("summary write failed");
}

int main(int argc,char**argv) {
  try {
    if(argc != 3) fail("usage: exact_search B output-directory");
    const u64 bound=std::stoull(argv[1]);
    if(bound<2 || bound>LIMIT) fail("B must satisfy 2 <= B <= 2^31");
    const fs::path dir=argv[2];
    if(fs::exists(dir) && !fs::is_empty(dir)) fail("output directory must be empty");
    fs::create_directories(dir);
    const auto start=std::chrono::steady_clock::now();
    std::array<u64,PARTITIONS> counts{};
    u64 last_state=0;
    std::cerr << "generating " << bound << " field powers into 256 exact buckets\n";
    generate(dir,bound,counts,last_state);
    u64 sum=0; for(u64 n:counts) sum+=n;
    if(sum!=bound) fail("partition counts do not cover full exponent range");
    std::cerr << "generation complete; exact radix sorting/checking\n";
    std::vector<u64> matches;
    for(unsigned p=0;p<PARTITIONS;++p) {
      const std::string path=bucket_path(dir,p);
      std::ifstream in(path,std::ios::binary);
      if(!in) fail("cannot open bucket for verification");
      const auto file_bytes=fs::file_size(path);
      if(file_bytes != 8 * counts[p]) fail("partition file size mismatch");
      std::vector<u64> v(counts[p]);
      in.read(reinterpret_cast<char *>(v.data()),(std::streamsize)file_bytes);
      if(in.gcount()!=(std::streamsize)file_bytes) fail("incomplete bucket read");
      in.close();
      for(u64 k:v) if((k>>52)!=p) fail("bucket membership check failed");
      sort_exact(v);
      for(size_t i=1;i<v.size();++i) if(v[i]==v[i-1]) {
        if(i>=2 && v[i]==v[i-2]) fail("unexpected triple-collision: audit field order");
        matches.push_back(v[i]);
      }
      // Once checked, the large raw bucket may be deleted safely. Retain summary only.
      if(!fs::remove(path)) fail("failed to remove verified bucket");
      if((p+1)%32==0) std::cerr << "verified " << p+1 << "/256 partitions; candidate pairs=" << matches.size() << "\n";
    }
    std::sort(matches.begin(),matches.end());
    if(std::adjacent_find(matches.begin(), matches.end())!=matches.end()) fail("collision key in distinct buckets");
    struct Hit {u64 key;u64 exponent;u64 state;};
    std::vector<Hit> hits; hits.reserve(matches.size()*2);
    u64 state=1;
    for(u64 exponent=1;exponent<=bound;++exponent) {
      state=mulX(state);
      const u64 k=state >> 1;
      if(std::binary_search(matches.begin(),matches.end(),k)) hits.push_back({k,exponent,state});
    }
    if(state!=last_state) fail("reconstruction ended at a different LFSR state");
    std::sort(hits.begin(),hits.end(),[](const Hit &a,const Hit &b){
      return a.key<b.key || (a.key==b.key && a.exponent<b.exponent);
    });
    if(hits.size()!=2*matches.size()) fail("each collision must correspond to exactly two states");
    std::vector<Pair> pairs;
    for(size_t i=0;i<hits.size();i+=2) {
      if(hits[i].key!=hits[i+1].key) fail("reconstruction keys mismatch");
      if((hits[i].state ^ hits[i+1].state)!=1) fail("not a valid trinomial state pair");
      const u64 a=hits[i].exponent, b=hits[i+1].exponent;
      if(!(0<a && a<b && b<=bound)) fail("invalid exponent order");
      pairs.push_back({a,b});
      std::cout << "SOLUTION a=" << a << " b=" << b << "\n";
    }
    std::sort(pairs.begin(),pairs.end(),[](const Pair &a,const Pair &b){return a.b<b.b;});
    const double secs=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    write_summary(dir,bound,counts,matches,pairs,last_state,secs);
    std::cout << "DONE B=" << bound << " matches=" << pairs.size() << " seconds=" << secs << "\n";
  } catch(const std::exception &e) {std::cerr << "ERROR " << e.what() << "\n";return 1;}
}
