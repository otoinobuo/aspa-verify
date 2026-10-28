"""Cross-check model.py against 'ASPA-based AS path verification examples' (Sriram, Borchert, Matejka; Oct 2026),
the document referenced as [aspa-examples] in Section 6.1 of draft-ietf-sidrops-aspa-verification."""
from model import bounds, verify, compress
T12={'A':{'C','D'},'B':{'E'},'C':{'F'},'D':{'F','G'},'G':set()}          # G lists only AS0
T3 ={'H':set(),'K':set(),'L':{'K'},'P':set(),'Q':set(),'R':{'Q'},'S':{'R'}}
# (table, row, receiver, AS path most-recent-first, downstream?, expected (N, max_up, max_down, min_up, min_down, outcome)); None = NA
rows=[
 ('T1',1,'G','FCA',False,(3,3,None,3,None,'Valid')),
 ('T1',2,'G','DCA',False,(3,2,None,2,None,'Invalid')),
 ('T1',3,'G','DFCA',False,(4,4,None,3,None,'Unknown')),
 ('T1',4,'C','DEB',False,(3,3,None,2,None,'Unknown')),
 ('T1',5,'C','ADEB',False,(4,3,None,2,None,'Invalid')),
 ('T1',6,'C','ADGEB',False,(5,3,None,2,None,'Invalid')),
 ('T1',7,'D','ACF',False,(3,2,None,1,None,'Invalid')),
 ('T1',8,'D','ACFG',False,(4,1,None,1,None,'Invalid')),
 ('T1',9,'D','EB',False,(2,2,None,2,None,'Valid')),
 ('T2',1,'B','EGFCA',True,(5,4,2,3,1,'Unknown')),
 ('T2',2,'B','EGDA',True,(4,3,2,3,1,'Valid')),
 ('T2',3,'B','EDCA',True,(4,2,2,2,1,'Unknown')),
 ('T2',4,'B','EGDCA',True,(5,2,2,2,1,'Invalid')),
 ('T2',5,'A','CFDG',True,(4,1,4,1,2,'Unknown')),
 ('T2',6,'A','DGEB',True,(4,3,2,2,2,'Valid')),
 ('T2',7,'A','CDGEB',True,(5,3,1,2,1,'Invalid')),
 ('T2',8,'D','FCA',True,(3,3,2,3,1,'Valid')),
 ('T2',9,'B','EA',True,(2,1,2,1,1,'Valid')),
 ('T2',10,'B','ECA',True,(3,2,2,2,1,'Valid')),
 ('T3',1,'K','JH',False,(2,1,None,1,None,'Invalid')),
 ('T3',2,'K','JH',False,(2,1,None,1,None,'Invalid')),
 ('T3',3,'L','KJH',True,(3,1,1,1,1,'Invalid')),
 ('T3',4,'R','QP',False,(2,1,None,1,None,'Invalid')),
 ('T3',5,'R','QP',True,(2,1,1,1,1,'Valid')),
 ('T3',6,'S','RQP',True,(3,1,2,1,2,'Valid')),
]
ok=bad=0
for tab,r,recv,p,down,exp in rows:
    spas=T3 if tab=='T3' else T12
    path=list(reversed(list(p)))            # origin-first
    A=compress(path); N=len(A); mu,nu,md,nd=bounds(spas,A); out=verify(spas,path,down)
    got=(N,mu,md if down else None,nu,nd if down else None,out)
    good = got==exp
    ok+=good; bad+= not good
    print(f'{tab} #{r:<2} {recv} <- {p:6} {"down" if down else "up  "} got {got} expected {exp} {"OK" if good else "MISMATCH"}')
print('match',ok,'mismatch',bad)
