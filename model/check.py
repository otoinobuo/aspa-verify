"""Exhaustive check on all labelled topologies with n ASes (relationship per unordered pair),
all simple AS paths, every receiver adjacent to the last hop, and every ASPA deployment subset."""
import itertools,sys,collections
from model import *
n=int(sys.argv[1]); with_rs=len(sys.argv)>2 and sys.argv[2]=='rs'
ases=list(range(n)); pairs=list(itertools.combinations(ases,2))
opts=[None,'prov','cust','peer']+(['rs','rsc'] if with_rs else [])
viol=collections.Counter(); ex={}; total=0
for lab in itertools.product(opts,repeat=len(pairs)):
    rel={}
    for (x,y),r in zip(pairs,lab):
        if r: rel[(x,y)]=r; rel[(y,x)]=INV[r]
    # an RS (non-transparent) must have only 'rsc' neighbours; RS-client relation only towards RSes
    if with_rs:
        rsset={y for (x,y),r in rel.items() if r=='rs'}
        if any(rel[(z,w)]!='rsc' for (z,w) in rel if z in rsset): continue
    truth_spas=spas_of(rel,ases)
    adj=collections.defaultdict(list)
    for (x,y) in rel: adj[x].append(y)
    for L in range(1,n):
        for path in itertools.permutations(ases,L):
            if any((path[i],path[i+1]) not in rel for i in range(L-1)): continue
            for recv in adj[path[-1]]:
                if recv in path: continue
                r_rel=rel[(recv,path[-1])]
                downstream = r_rel=='prov'
                truth=leak_free(rel,path,recv)
                for k in range(0,len(path)+1):
                    for dep in itertools.combinations(path,k):
                        spas={x:truth_spas[x] for x in dep}
                        out=verify(spas,path,downstream); total+=1
                        full=(k==len(path))
                        key=None
                        if out=='Invalid' and truth: key='false positive (Invalid on leak-free)'
                        elif out=='Valid' and not truth: key='Valid on leak'
                        elif full and out=='Unknown': key='Unknown under full deployment'
                        elif full and out=='Valid' and not truth: key='full deployment missed leak'
                        if key:
                            viol[key]+=1
                            ex.setdefault(key,(lab,path,recv,r_rel,dep,out,truth))
print('n=%d rs=%s checked %d cases'%(n,with_rs,total))
for k,v in viol.items(): print(' ',k,v,'e.g.',ex[k])
if not viol: print('  no violations')
