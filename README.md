 
## Welcome to TLA<sup>+</sup> Benchmarks 

The page **TLA<sup>+</sup> Benchmarks** is a library of TLA<sup>+</sup> specifications for distributed algorithms. The webpage supplies the TLA<sup>+</sup> community with:

- A comprehensive library of the TLA<sup>+</sup> specifications that are available today, in order to provide an overview of how to specify an algorithm in TLA<sup>+</sup>.
- A comprehensive list of references and other interesting information for each problem.

Do you have your own case study that you like to share with the community? Send a pointer to us and we will include it in the repository. Your specifications will help the community in improving the tools for TLA<sup>+</sup> analysis.

### List of benchmarks

| No | Name  | Short description | Fault models	| Properties | Extended modules | 
| :--: | ----| -------------------------------------------------------- | :--------: | ---------  | 
|	1	| <a href="http://list.cs.northwestern.edu/802.16/">802.16</a> | <a href="https://ieeexplore.ieee.org/document/5062485/">IEEE 802.16 WiMAX Protocols</a>, <a href="https://www.cs.northwestern.edu/~ychen/Papers/npsec06.pdf">Checking of 802.16 throung TLA</a>  | no faults | DoS vulnerability | Int, Seq, FinSet | 
|	2	| <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/aba-asyn-byz">aba-asyn-byz</a>	|	<a href="https://dl.acm.org/citation.cfm?id=214134">Bracha and Toueg's asynchronous Byzantine agreement</a> | Byzantine | correctness, agreement, unforgeability	|	Nat | 
|	3	| <a href="https://members.loria.fr/SMerz/talks/argentina2005/Charpentier/charpov/Teaching/CS-986/TLC/">acp-sb</a> | <a href="https://dl.acm.org/citation.cfm?id=302436">Babaoglu and Toueg's non-blocking atomic commitment</a> with a simple broadcast | clean crashes | AC1-AC5, no recovery, termincation | default theories	|	
|	4	| <a href="https://members.loria.fr/SMerz/talks/argentina2005/Charpentier/charpov/Teaching/CS-986/TLC/">acp-nb</a> | <a href="https://dl.acm.org/citation.cfm?id=302436">Non-blocking atomic commitment</a> with a reliable broadcast | clean crashes | AC1-AC5, termination, AllAbort, AllCommit | default theories |				
|	5	| <a href="https://members.loria.fr/SMerz/talks/argentina2005/Charpentier/charpov/Teaching/CS-986/TLC/">acp-nb-wrong</a> | Wrong version of <a href="https://dl.acm.org/citation.cfm?id=302436">non-blocking atomic commitment</a> with a reliable broadcast | clean crashes | AC1-AC5, termination, AllAbort, AllCommit | default theories |				
|	6	| <a href="http://hurault.perso.enseeiht.fr/asynchronousCommunication/">async-comm</a> | <a href="https://link.springer.com/article/10.1007/s00165-016-0379-x">The diversity of asynchronous communication</a> | &#10067; | compatibility, termination |	Nat	|		
|	7	| <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/bcastByz">bcastByz</a> | <a href="https://link.springer.com/article/10.1007/BF01667080">Asynchronous reliable broadcast</a>	(Figure 7) | Byzantine | correctness, relay, unforgeability |	Nat,  FinSet	|	
|	8	| <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/bcastFolklore">bcastFolklore</a>	| <a href="https://dl.acm.org/citation.cfm?id=226647">Folklore reliable broadcast</a> (Figure 4) | clean crashes	| correctness, relay, unforgeability |	Nat	|
|	9	| <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/bosco">bosco</a>	| <a href="https://link.springer.com/chapter/10.1007/978-3-540-87779-0_30">One-Step Byzantine asynchronous consensus</a> |	Byzantine | Lemma3, Lemma4, OneStep0, OneStep1 | Nat, FinSet |		
|	10	| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/Bakery-Boulangerie">Boulangerie</a> | <a href="https://dl.acm.org/citation.cfm?id=2950394">A variant of the bakery algorithm</a>	| no faults | mutex |	Int	|	
|	11	| <a href="http://lamport.azurewebsites.net/tla/byzpaxos.html">byzpaxos</a>	| <a href="http://lamport.azurewebsites.net/tla/byzsimple.pdf">Byzantizing Paxos by Refinement</a>	| Byzantine | Safety | Int, FinSet	|	
|	12	| <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/c1cs">c1cs</a> | <a href="https://link.springer.com/chapter/10.1007/3-540-44743-1_4">Consensus in one communication step</a>	| clean crashes	| validity, agreement,<br/>weak-agreement,<br/> termination |	Int, FinSet |	
|	13	| <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/cbc_max">cbc_max</a>	| <a href="https://ieeexplore.ieee.org/document/1209964/">Condition-based consensus</a>	| Byzantine	| validity, agreement, termination	| Int, FinSet |
|	14	| <a href="https://github.com/nano-o/Caesar">Caesar</a> | <a href="https://ieeexplore.ieee.org/document/8023110/">Multi-leader generalized consensus protocol</a> | clean crashes | GraphInvariant,<br/> agreement |	FinSet, Seq, Int |			
|	15	| <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/cf1s-folklore">cf1s-folklore</a>	| <a href="https://ieeexplore.ieee.org/abstract/document/1633503/">One-step consensus with zero-degradation</a>	| clean crashes	| OneStep0, OneStep1 |	Nat
|	16	| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/chang_roberts">ChangRoberts</a>	| <a href="https://dl.acm.org/citation.cfm?id=359108">Leader election in a ring</a> | no faults | termination | Nat, Seq |			
|	17	| DataPort | <a href="https://ieeexplore.ieee.org/iel7/7858577/7862346/07862411.pdf">Dataport protocal 505.89PT</a>, only PDF files | no faults | deadlock | Int, Seq |				
|	18	| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/dijkstra-mutex">dijkstra-mutex</a>	| <a href="https://dl.acm.org/citation.cfm?id=365617">Dijkstra's mutual exclusion algorithm</a>	| no faults | mutex, starvation,<br/> termination | Int |		
|	19	| <a href="https://github.com/nano-o/MultiPaxos/blob/master/DiskPaxos.tla">diskpaxos</a>	| <a href="https://lamport.azurewebsites.net/pubs/disk-paxos.pdf">Disk Paxos</a> | crashes, inaccessibility | SynodSpec | Int	|		
|	20	| <a href="https://github.com/efficient/epaxos">egalitarian-paxos</a> | <a href="https://dl.acm.org/citation.cfm?id=2517350">Leaderless replication protocol based on Paxos</a> | crashes | nontriviality, stability, consistency |	Nat, FinSet	|		
|	21	| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/ewd840">ewd840</a>	| <a href="https://www.cs.utexas.edu/users/EWD/ewd08xx/EWD840.PDF">Dijkstra's algorithm for termination detection in a ring</a>	 | no faults | termination | Nat |		
|	22	| <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/detector_chan96">detector_chan96</a>	| <a href="https://dl.acm.org/citation.cfm?id=226647">Chandra and Toueg's eventually perfect failure detector</a>	| clean crashes	|	strong completeness,<br/> eventual strong accuracy | Int, FinSet |
|	23	| fastpaxos | <a href="https://www.microsoft.com/en-us/research/publication/fast-paxos/">An extension of the classic Paxos algorithm</a>, only PDF files | crashes, lost/duplicated messages | nontriviality, consistency |	Nat, FinSet	|		
|	24	| <a href="https://github.com/fpaxos/fpaxos-tlaplus">fpaxos</a>	| <a href="https://arxiv.org/pdf/1608.06696v1.pdf">A variant of Paxos with flexible quorums</a> | crashes, lost/duplicated messages | agreed, SafeValue |	Int	|	
|	25	| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/lamport_mutex">lamport_mutex</a>	| <a href="https://lamport.azurewebsites.net/pubs/time-clocks.pdf">Lamport's mutual exclusion</a>	| no faults | mutex | Nat, Seq |		
|	26	| L1 | <a href="https://www.microsoft.com/en-us/research/publication/the-data-center-network-l1-switch-protocol/">Data center network L1 switch protocol</a>, only PDF files	| &#10067; | AllLinkEvQuiet, AllNodeInSlotEvAvail, AllNodeOutSlotEvAvail |	FinSet, Nat, Seq |		
|	27	| <a href="https://losa.fr/research/leaderless/">leaderless</a>	| <a href="https://www.ssrg.ece.vt.edu/papers/2016_podc.pdf">Leaderless generalized-consensus algorithms</a> | clean crashes | nontriviality, consistency, stability |	FinSet, Int, Seq |		
|	28	| <a href="https://losa.fr/research/assignment/">losa_ap</a>	| <a href="https://dl.acm.org/citation.cfm?id=3154303">The assignment problem</a>, a variant of the allocation problem | &#10067; | fairness, consistency, correctness, termination |	FinSet, Nat, Seq  |		
|	29	| <a href="https://www.losa.fr/Thesis.pdf">losa_rda</a>	| <a href="https://www.losa.fr/Thesis.pdf">Applying peculative linearizability to fault-tolerant message-passing algorithms and shared-memory consensus</a>, only PDF files | crashes,<br/> lost messages | correctness, refinement mapping | FinSet, Nat, Seq	|		
|	30	| <a href="https://losa.fr/M2Paxos/">m2paxos</a>	| <a href="https://ieeexplore.ieee.org/document/7579738/">Multi-leader consensus protocols</a> | clean crashes | correctness | Int, Seq, FinSet	|		
|	31	| <a href="https://github.com/nano-o/MultiPaxos">MultiPaxos</a>	| <a href="https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2005-33.pdf">The abstract specification of Generalized Paxos</a> | crashes, lost/duplicated messages | correctness | Int, FinSet	|		
|	32	| naiad	| <a href="https://www.microsoft.com/en-us/research/wp-content/uploads/2013/02/paper.pdf">Naiad clock protocol</a>, only PDF files	| no faults | correctness |	Int, Seq, FinSet |	
|	33	| <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/nbacc_ray97">nbacc\_ray97</a>	| <a href="https://ieeexplore.ieee.org/document/648067/">Asynchronous non-blocking atomic commit</a>	| clean crashes	|	validity, nontriviality, termination | Nat, FinSet
|	34	| <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/nbacg_guer01">nbacg\_guer01</a>	| <a href="dl.acm.org/citation.cfm?id=380061">Asynchronous non-blocking atomic commit</a> | clean crashes	| agreement	, validity,<br/> integrity, termination | Nat, FinSet	|
|	35	| <a href="http://www.steffen-zschaler.de/publications/NfC04/">nfc04</a>	| <a href="https://link.springer.com/article/10.1007/s10270-009-0115-6">Non-functional properties of component-based software systems</a> | no faults | ExecutionTimesOk, TimedCPUScheduler | Real, Nat |			
|	36	| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/Paxos">paxos</a>	| <a href="https://lamport.azurewebsites.net/pubs/lamport-paxos.pdf">Paxos consensus algorithm</a>	| crashes, lost/duplicated messages | TypeOK , Success | Int, FinSet	|	
|	37	| <a href="https://github.com/ongardie/raft.tla">raft</a>	| <a href="https://raft.github.io/raft.pdf">Raft consensus algorithm</a> | crashes, lost/duplicated messages | deadlock | FinSet, Nat, Seq |			
|	38	| <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/spanning">spanning</a>	| Spanning tree broadcast algorithm in Attiya and Welch's book | no faults | OneParent, termination |	Int	|	
|	39	| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/transaction_commit">transaction_commit</a>	| <a href="https://dl.acm.org/citation.cfm?id=1132867">Consensus on transaction commit</a> | crashes, lost/duplicated messages | consistent, TypeOK |	Int	|	
|	40	| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/TwoPhase">TwoPhase</a>	| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/TwoPhase">Two-phase handshaking</a> | no faults | Inv |	Nat	|	
|	41	| <a href="https://github.com/nano-o/Distributed-termination-detection">Termination</a>	| <a href="https://link.springer.com/article/10.1007/BF01782776">Channel counting algorithm</a> | idle | termination |	FinSet, Bags, Nat	|

### Support or Contact

Do you have any questions? Please contact <a href="mailto: tran@forsyte.ac.at">Thanh-Hai Tran</a>.
