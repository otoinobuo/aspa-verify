"""Exhaustive check of ASRA (Alg A/B) for false positives (Invalid on a leak-free path) with correct registrations."""
import itertools,sys,collections
from model import *
from asra import verify_asra
n=int(sys.argv[1])
ases=list(range(n)); pairs=list(itertools.combinations(ases,2))
opts=[None,'prov','cust','peer']
fp=collections.Counter(); ex={}; total=0; lost=collections.Counter()
for lab in itertools.product(opts,repeat=len(pairs)):
    rel={}
    for (x,y),r in zip(pairs,lab):
        if r: rel[(x,y)]=r; rel[(y,x)]=INV[r]
    tspas=spas_of(rel,ases)
    tasra={x:{'C':{y for (z,y),r in rel.items() if z==x and r=='cust'},'LP':{y for (z,y),r in rel.items() if z==x and r=='peer'}} for x in ases}
    adj=collections.defaultdict(list)
    for (x,y) in rel: adj[x].append(y)
    for L in range(2,n):
        for path in itertools.permutations(ases,L):
            if any((path[i],path[i+1]) not in rel for i in range(L-1)): continue
            for recv in adj[path[-1]]:
                if recv in path or rel[(recv,path[-1])]!='prov': continue      # downstream only
                truth=leak_free(rel,path,recv)
                for k in range(len(path)+1):
                    for dep in itertools.combinations(path,k):
                        aspa={x:tspas[x] for x in dep}
                        for k2 in range(len(dep)+1):
                            for dep2 in itertools.combinations(dep,k2):      # ASRA adopters must have ASPA
                                asra={x:tasra[x] for x in dep2}
                                for alg in 'AB':
                                    total+=1
                                    base=verify(aspa,path,True)
                                    o=verify_asra(aspa,asra,path,True,alg)
                                    if o=='Invalid' and truth:
                                        fp[alg]+=1; ex.setdefault(alg,(dict((p,rel[p]) for p in rel if p[0]<p[1]),path,recv,sorted(dep),sorted(dep2),base,o))
                                    if base=='Invalid' and o!='Invalid': lost[alg]+=1
print('n=%d checked %d'%(n,total))
for a in 'AB': print(' Alg',a,'false positives:',fp[a],'| ASPA-Invalid turned non-Invalid:',lost[a]); print('   e.g.',ex.get(a))
