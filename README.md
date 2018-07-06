
## Welcome to TLA<sup>+</sup> Benchmarks 

The page **TLA<sup>+</sup> Benchmarks** is a library of TLA<sup>+</sup> specifications for distributed algorithms. The webpage supplies the TLA<sup>+</sup> community with:

- A comprehensive library of the TLA<sup>+</sup> specifications that are available today, in order to provide an overview of how to specify an algorithm in TLA<sup>+</sup>.
- A comprehensive list of references and other interesting information for each problem.

We encourage the submission of new challenging TLA<sup>+</sup> benchmarks.

### List of benchmarks

| Name 												| Short description 																			| Failures 			| Properties				|
| ----| ----| :--------: | ---------------------- |
| <a href="http://list.cs.northwestern.edu/802.16/">802.16</a> | <a href="https://ieeexplore.ieee.org/document/5062485/">IEEE 802.16 WiMAX Protocols</a><br/> <a href="https://www.cs.northwestern.edu/~ychen/Papers/npsec06.pdf"> Checking of 802.16 throung TLA</a> | &#10067; | deadlock<br/> correctness |
| <a href="https://github.com/hiocean/tlabenchmarks/">aba-asyn-byz</a>	|	<a href="https://dl.acm.org/citation.cfm?id=214134">Asynchronous Byzantine agreement</a> | Byzantine | unforgeability<br/> correctness<br/>agreement	|
| <a href="https://members.loria.fr/SMerz/talks/argentina2005/Charpentier/charpov/Teaching/CS-986/TLC/">acp-sb</a> | <a href="https://dl.acm.org/citation.cfm?id=302436">Babaoglu and Toueg's non-blocking atomic commitment</a> with a simple broadcast | clean crashes | AC1-AC5<br/>no recovery<br/>termincation |
| <a href="https://members.loria.fr/SMerz/talks/argentina2005/Charpentier/charpov/Teaching/CS-986/TLC/">acp-nb</a> | <a href="https://dl.acm.org/citation.cfm?id=302436">Non-blocking atomic commitment</a>  with a reliable broadcast | clean crashes | AC1-AC5<br/> termination<br/> AllAbort<br/> AllCommit |
| <a href="https://members.loria.fr/SMerz/talks/argentina2005/Charpentier/charpov/Teaching/CS-986/TLC/">acp-nb-wrong</a> | Wrong version of <a href="https://dl.acm.org/citation.cfm?id=302436">non-blocking atomic commitment</a> with a reliable broadcast | clean crashes | AC1-AC5<br/> termination<br/> AllAbort<br/> AllCommit |
| <a href="https://github.com/hiocean/tlabenchmarks/">spanning</a>	| Spanning tree broadcast algorithm in Attiya and Welch's book | &#10060; | OneParent <br/>termination |
| <a href="http://hurault.perso.enseeiht.fr/asynchronousCommunication/">async-comm</a> | <a href="https://link.springer.com/article/10.1007/s00165-016-0379-x">The diversity of asynchronous communication</a> | &#10067; | compatibility<br/>termination |
| <a href="https://github.com/hiocean/tlabenchmarks/">bcastByz</a> | <a href="https://link.springer.com/article/10.1007/BF01667080">Asynchronous reliable broadcast</a>	(Figure 7) | Byzantine | unforgeability<br/>correctness<br/>relay |
| <a href="https://github.com/hiocean/tlabenchmarks/">bcastFolklore</a>	| <a href="https://dl.acm.org/citation.cfm?id=226647">Folklore reliable broadcast</a> (Figure 4) | clean crashes	| unforgeability <br/> correctness <br/> relay |
| <a href="https://github.com/hiocean/tlabenchmarks/">bosco</a>	| <a href="https://link.springer.com/chapter/10.1007/978-3-540-87779-0_30">One-Step Byzantine asynchronous consensus</a> |	Lemma3 | Byzantine <br/> Lemma4 <br/> OneStep0 <br/> OneStep1 |
| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/Bakery-Boulangerie">Boulangerie</a> | <a href="https://dl.acm.org/citation.cfm?id=2950394">A variant of the bakery algorithm</a>	| &#10060; | mutex |
| <a href="https://github.com/hiocean/tlabenchmarks/">c1cs</a> | <a href="https://link.springer.com/chapter/10.1007/3-540-44743-1_4">Consensus in one communication step</a>	| clean crashes	| validity <br/> agreement <br/> weak-agreement <br/> termination |
| <a href="https://github.com/hiocean/tlabenchmarks/">cbc_max</a>	| <a href="https://ieeexplore.ieee.org/document/1209964/">Condition-based consensus</a>	| Byzantine	| validity <br/> agreement <br/> termination	|
| <a href="https://arxiv.org/pdf/1704.03319.pdf">Caesar</a> | <a href="https://ieeexplore.ieee.org/document/8023110/">Multi-leader generalized consensus protocol</a>, only PDF files | clean crashes | GraphInvariant<br/>agreement |
| <a href="https://github.com/hiocean/tlabenchmarks/">cf1s-folklore-onestep</a>	| <a href="https://ieeexplore.ieee.org/abstract/document/1633503/">One-step consensus with zero-degradation</a>	| clean crashes	| OneStep0 <br/> OneStep1 |
| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/chang_roberts">ChangRoberts</a>	| <a href="https://dl.acm.org/citation.cfm?id=359108">Leader election in a ring</a> | &#10060; | termination |
| DataPort										| <a href="https://ieeexplore.ieee.org/iel7/7858577/7862346/07862411.pdf">Dataport protocal 505.89PT</a>, only PDF files | &#10060; | deadlock |
| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/dijkstra-mutex">dijkstra-mutex</a>	| <a href="https://dl.acm.org/citation.cfm?id=365617">Dijkstra's mutual exclusion algorithm</a>	| &#10060; | mutex <br/> deadloc <br/> starvation <br> termination |
| diskpaxos	| <a href="https://lamport.azurewebsites.net/pubs/disk-paxos.pdf"> Disk Paxos</a>, only PDF files | non-Byzantine | SynodSpec |
| <a href="https://github.com/efficient/epaxos">egalitarian-paxos</a> |  <a href="https://dl.acm.org/citation.cfm?id=2517350">Leaderless replication protocol based on Paxos</a> | crashes | nontriviality <br/> stability <br/> consistency |
| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/ewd840">ewd840</a>	| <a href="https://www.cs.utexas.edu/users/EWD/ewd08xx/EWD840.PDF">Dijkstra's algorithm for termination detection in a ring</a>	 | &#10060;  | termination |
| <a href="https://github.com/hiocean/tlabenchmarks/">detector_chan96</a>	| <a href="https://dl.acm.org/citation.cfm?id=226647">Chandra and Toueg's eventually perfect failure detector</a>	| clean crashes	|	strong completeness <br/> eventual strong accuracy |
| fastpaxos | <a href="https://www.microsoft.com/en-us/research/publication/fast-paxos/">An extension of the classic Paxos algorithm </a>, only PDF files | non-Byzantine | nontriviality <br/> consistency |
| <a href="https://github.com/fpaxos/fpaxos-tlaplus">fpaxos</a>	| <a href="https://arxiv.org/pdf/1608.06696v1.pdf">A variant of Paxos with flexible quorums</a> | non-Byzantine | agreed <br/> SafeValue |
| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/lamport_mutex">lamport_mutex</a>	| <a href="https://lamport.azurewebsites.net/pubs/time-clocks.pdf">Lamport's mutual exclusion</a>	| &#10060; | mutex |
| L1 | <a href="https://www.microsoft.com/en-us/research/publication/the-data-center-network-l1-switch-protocol/">Data center network L1 switch protocol</a>, only PDF files	| &#10067; | AllLinkEvQuiet <br/> AllNodeInSlotEvAvail <br/> AllNodeOutSlotEvAvail |
| <a href="https://losa.fr/research/leaderless/">leaderless</a>	| <a href="dl.acm.org/ft_gateway.cfm?id=2933072&type=pdf">Leaderless generalized-consensus algorithms</a> | clean crashes |  nontriviality <br/> consistency <br/> stability |
| <a href="https://losa.fr/research/assignment/">losa_ap</a>	| <a href="https://dl.acm.org/citation.cfm?id=3154303">The assignment problem</a>, a variant of the allocation problem | &#10067; | fairness <br/> consistency <br/> correctness <br/> termination |
| <a href="">losa_rda</a>	| <a href="">&#10067;</a> | &#10067; | &#10067; |
| <a href="https://losa.fr/M2Paxos/">m2paxos</a>	| <a href="https://ieeexplore.ieee.org/document/7579738/">Multi-leader consensus protocols</a> | clean crashes | correctness |
| naiad	| <a href="https://www.microsoft.com/en-us/research/wp-content/uploads/2013/02/paper.pdf">Naiad clock protocol</a>, only PDF files	| &#10060; | correctness |
| <a href="https://github.com/hiocean/tlabenchmarks/">nbacc-ray97</a>	| <a href="https://ieeexplore.ieee.org/document/648067/">Asynchronous non-blocking atomic commit</a>	| clean crashes	|	validity <br/> nontriviality <br/> termination |
| <a href="https://github.com/hiocean/tlabenchmarks/">nbacg-guer01</a>	| <a href="dl.acm.org/citation.cfm?id=380061">Asynchronous non-blocking atomic commit</a> | clean crashes	| agreement	<br/> validity <br/> integrity	<br/> termination | 
| <a href="http://www.steffen-zschaler.de/publications/NfC04/">nfc04</a>	| <a href="https://link.springer.com/article/10.1007/s10270-009-0115-6">Non-functional properties of component-based software systems</a> | &#10060; | ExecutionTimesOk <br/> TimedCPUScheduler |
| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/Paxos">paxos</a>	| <a href="https://lamport.azurewebsites.net/pubs/lamport-paxos.pdf"> Paxos consensus algorithm</a>	| non-Byzantine | TypeOK  <br/> Success  <br/> |
| <a href="https://github.com/ongardie/raft.tla">raft</a>	| <a href="https://raft.github.io/raft.pdf">Raft consensus algorithm</a> | non-Byzantine | deadlock |
| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/transaction_commit">transaction_commit</a>	| <a href="https://dl.acm.org/citation.cfm?id=1132867">Consensus on transaction commit</a> | non-Byzantine | consistent <br/> TypeOK |
| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/TwoPhase">TwoPhase</a>	| <a href="https://github.com/tlaplus/Examples/tree/master/specifications/TwoPhase">Two-phase handshaking</a> | &#10067; | Inv |

### Support or Contact

Do you have any questions? Please contact  <a href="mailto: tran@forsyte.ac.at">Thanh-Hai Tran</a>.
