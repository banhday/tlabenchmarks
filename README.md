 
## Welcome to TLA<sup>+</sup> Benchmarks 

The page **TLA<sup>+</sup> Benchmarks** is a library of TLA<sup>+</sup> specifications for distributed algorithms. The webpage supplies the TLA<sup>+</sup> community with:

- A comprehensive library of the TLA<sup>+</sup> specifications that are available today, in order to provide an overview of how to specify an algorithm in TLA<sup>+</sup>.
- A comprehensive list of references and other interesting information for each problem.

Do you have your own case study that you like to share with the community? Send a pointer to us and we will include it in the repository. Your specifications will help the community in improving the tools for TLA<sup>+</sup> analysis.

## List of benchmarks

| No 	 | Name  | Short description 																				| Spec's authors	| TLAPS Proof | TLC Check | Used modules |
| :--: | ----  | -------------------------------------------------------- | --------------- | :---------: | :-------: | ------------ |
| 1 | 2PCwithBTM | <a href="https://github.com/muratdem/PlusCal-examples/blob/master/2PCTM/">A modified version of  P2TCommit (Gray & Lamport, 2006)</a> | Murat Demirbas |  | &#10004; | FinSet, Int, Seq | 
| 2 | 802.16 | <a href="http://list.cs.northwestern.edu/802.16/">IEEE 802.16 WiMAX Protocols</a> | Prasad Narayana, Ruiming Chen, Yao Zhao, Yan Chen, Zhi (Judy) Fu, and Hai Zhou |  | &#10004; | Int, Seq, FinSet | 
| 3 | aba-asyn-byz | <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/aba-asyn-byz">Asynchronous Byzantine agreement (Bracha & Toueg, 1985)</a> | Thanh Hai Tran, Igor Konnov, Josef Widder |  | &#10004; | Nat | 
| 4 | acp-nb | <a href="https://members.loria.fr/SMerz/talks/argentina2005/Charpentier/charpov/Teaching/CS-986/TLC/">Non-blocking atomic commitment with a reliable broadcast (Babaoğlu & Toueg, 1993)</a> | Stephan Merz |  | &#10004; | default theories | 
| 5 | acp-nb-wrong | <a href="https://members.loria.fr/SMerz/talks/argentina2005/Charpentier/charpov/Teaching/CS-986/TLC/">Wrong version of the non-blocking atomic commitment with a reliable broadcast (Babaoğlu & Toueg, 1993)</a> | Stephan Merz |  | &#10004; | default theories | 
| 6 | acp-sb | <a href="https://members.loria.fr/SMerz/talks/argentina2005/Charpentier/charpov/Teaching/CS-986/TLC/">Non-blocking atomic commitment with a simple broadcast (Babaoğlu & Toueg, 1993)</a> | Stephan Merz |  | &#10004; | default theories | 
| 7 | allocator | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/allocator">Specification of a resource allocator</a> | Stephan Merz |  | &#10004; | FinSet | 
| 8 | async-comm | <a href="http://hurault.perso.enseeiht.fr/asynchronousCommunication/">The diversity of asynchronous communication (Chevrou et al., 2016) </a> | Florent Chevrou, Aurélie Hurault, Philippe Quéinnec |  | &#10004; | Nat | 
| 9 | bcastByz | <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/bcastByz">Asynchronous reliable broadcast - Figure 7 (Srikanth & Toeug, 1987)</a> | Thanh Hai Tran, Igor Konnov, Josef Widder | &#10004; | &#10004; | Nat, FinSet | 
| 10 | bcastFolklore | <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/bcastFolklore">Folklore reliable broadcast - Figure 4 (Chandra and Toueg, 1996)</a> | Thanh Hai Tran, Igor Konnov, Josef Widder | &#10004; | &#10004; | Nat | 
| 11 | bosco | <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/bosco">One-Step Byzantine asynchronous consensus (Song & Renesse, 2008)</a> | Thanh Hai Tran, Igor Konnov, Josef Widder |  | &#10004; | Nat, FinSet | 
| 12 | Boulangerie | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/Bakery-Boulangerie">A variant of the bakery algorithm (Yoram & Patkin, 2015)</a> | Stephan Merz | &#10004; | &#10004; | Int | 
| 13 | byihive | <a href="https://github.com/byisystems/byihive">Based on RFC3506 - Requirements and Design for Voucher Trading System (Fujimura & Eastlake) </a> | Santhosh Raju |  | &#10004; | default theories | 
| 14 | byzpaxos | <a href="http://lamport.azurewebsites.net/tla/byzpaxos.html">Byzantizing Paxos by Refinement (Lamport, 2011)</a> | Leslie Lamport? |  | &#10004; | Int, FinSet | 
| 15 | c1cs | <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/c1cs">Consensus in one communication step (Brasileiro et al., 2001)</a> | Thanh Hai Tran, Igor Konnov, Josef Widder |  | &#10004; | Int, FinSet | 
| 16 | Caesar | <a href="https://github.com/nano-o/Caesar">Multi-leader generalized consensus protocol (Arun et al., 2017)</a> | Giuliano Losa |  | &#10004; | FinSet, Seq, Int | 
| 17 | CarTalkPuzzle | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/CarTalkPuzzle">A TLA+ specification of the solution to a nice puzzle.</a> |  |  | &#10004; | Int | 
| 18 | CASPaxos | <a href="https://github.com/tschottdorf/caspaxos-tla">An extension of the single-decree Paxos algorithm to a compare-and-swap type register (Rystsov)</a> | Tobias Schottdorf |  | &#10004; | Int, FinSet | 
| 19 | cbc_max | <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/cbc_max">Condition-based consensus (Mostefaoui et al., 2003)</a> | Thanh Hai Tran, Igor Konnov, Josef Widder |  | &#10004; | Int, FinSet | 
| 20 | cf1s-folklore | <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/cf1s-folklore">One-step consensus with zero-degradation (Dobre & Suri, 2006)</a> | Thanh Hai Tran, Igor Konnov, Josef Widder |  | &#10004; | Nat | 
| 21 | ChangRoberts | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/chang_roberts">Leader election in a ring (Chang & Rosemary, 1979)</a> | Stephan Merz |  | &#10004; | Nat, Seq | 
| 22 | DataPort | <a href="https://ieeexplore.ieee.org/iel7/7858577/7862346/07862411.pdf">Dataport protocal 505.89PT, only PDF files (Biggs & Noriaki, 2016)</a> | Geoffrey Biggs, Noriaki Ando |  |  | Int, Seq | 
| 23 | detector_chan96 | <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/detector_chan96">Chandra and Toueg’s eventually perfect failure detector</a> | Thanh Hai Tran, Igor Konnov, Josef Widder |  | &#10004; | Int, FinSet | 
| 24 | DieHard | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/DieHard">A very elementary example based on a puzzle from a movie</a> |  |  | &#10004; | Nat | 
| 25 | dijkstra-mutex | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/dijkstra-mutex">Mutual exclusion algorithm (Dijkstra, 1965)</a> | Markus Alexander Kuppe |  | &#10004; | Int | 
| 26 | diskpaxos | <a href="https://github.com/nano-o/MultiPaxos/blob/master/DiskPaxos.tla">Disk Paxos (Gafni & Lamport, 2003)</a> | Giuliano Losa |  | &#10004; | Int | 
| 27 | egalitarian-paxos | <a href="https://github.com/efficient/epaxos">Leaderless replication protocol based on Paxos (Moraru et al., 2013)</a> | Iulian Moraru |  | &#10004; | Nat, FinSet | 
| 28 | ewd840 | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/ewd840">Termination detection in a ring (Dijkstra et al., 1986)</a> | Stephan Merz | &#10004; | &#10004; | Nat | 
| 29 | fastpaxos | <a href="https://www.microsoft.com/en-us/research/publication/fast-paxos/">An extension of the classic Paxos algorithm, only PDF files (Lamport, 2006)</a> | Heidi Howard |  |  | Nat, FinSet | 
| 30 | fpaxos | <a href="https://github.com/fpaxos/fpaxos-tlaplus">A variant of Paxos with flexible quorums (Howard et al., 2017)</a> | Heidi Howard |  | &#10004; | Int | 
| 31 | HLC | <a href="https://github.com/muratdem/HLC">Hybrid logical clocks and hybrid vector clocks (Demirbas et al., 2014)</a> | Murat Demirbas |  | &#10004; | Int | 
| 32 | L1 | <a href="https://www.microsoft.com/en-us/research/publication/the-data-center-network-l1-switch-protocol/">Data center network L1 switch protocol, only PDF files (Thacker)</a> | Tom Rodeheffer |  |  | FinSet, Nat, Seq | 
| 33 | lamport_mutex | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/lamport_mutex">Mutual exclusion (Lamport, 1978)</a> | Stephan Merz | &#10004; | &#10004; | Nat, Seq | 
| 34 | leaderless | <a href="https://losa.fr/research/leaderless/">Leaderless generalized-consensus algorithms (Losa, 2016)</a> | Giuliano Losa |  | &#10004; | FinSet, Int, Seq | 
| 35 | losa_ap | <a href="https://losa.fr/research/assignment/">The assignment problem, a variant of the allocation problem (Delporte-Gallet, 2018)</a> | Giuliano Losa |  | &#10004; | FinSet, Nat, Seq | 
| 36 | losa_rda | <a href="https://www.losa.fr/Thesis.pdf">Applying peculative linearizability to fault-tolerant message-passing algorithms and shared-memory consensus, only PDF files (Losa, 2014)</a> | Giuliano Losa |  |  | FinSet, Nat, Seq | 
| 37 | m2paxos | <a href="https://losa.fr/M2Paxos/">Multi-leader consensus protocols (Peluso et al., 2016)</a> | Giuliano Losa |  | &#10004; | Int, Seq, FinSet | 
| 38 | mongo-repl-tla | <a href="https://github.com/visualzhou/mongo-repl-tla">A simplified part of Raft in MongoDB (Ongaro, 2014)</a> | Siyuan Zhou |  | &#10004; | FinSet, Nat, Seq | 
| 39 | MultiPaxos | <a href="https://github.com/nano-o/MultiPaxos">The abstract specification of Generalized Paxos (Lamport, 2004)</a> | Giuliano Losa |  | &#10004; | Int, FinSet | 
| 40 | N-Queens | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/N-Queens">The N queens problem</a> | Stephan Merz |  | &#10004; | Nat, Seq | 
| 41 | naiad | <a href="https://www.microsoft.com/en-us/research/wp-content/uploads/2013/02/paper.pdf">Naiad clock protocol, only PDF files (Murray et al., 2013)</a> | Tom Rodeheffer |  | &#10004; | Int, Seq, FinSet | 
| 42 | nbacc_ray97 | <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/nbacc_ray97">Asynchronous non-blocking atomic commit (Raynal, 1997)</a> | Thanh Hai Tran, Igor Konnov, Josef Widder |  | &#10004; | Nat, FinSet | 
| 43 | nbacg_guer01 | <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/nbacg_guer01">On the hardness of failure-sensitive agreement problems (Guerraoui, 2001)</a> | Thanh Hai Tran, Igor Konnov, Josef Widder |  | &#10004; | Nat, FinSet | 
| 44 | nfc04 | <a href="http://www.steffen-zschaler.de/publications/NfC04/">Non-functional properties of component-based software systems (Zschaler, 2010)</a> | Steffen Zschaler |  | &#10004; | Real, Nat | 
| 45 | paxos | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/Paxos">Paxos consensus algorithm (Lamport, 1998)</a> | Leslie Lamport? |  | &#10004; | Int, FinSet | 
| 46 | Prisoners | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/Prisoners">A puzzle was presented on an American radio program.</a> |  |  | &#10004; | Nat, FinSet | 
| 47 | raft | <a href="https://github.com/ongardie/raft.tla">Raft consensus algorithm (Ongaro, 2014)</a> | Diego Ongaro |  | &#10004; | FinSet, Nat, Seq | 
| 48 | SnapshotIsolation | <a href="https://github.com/sanjosh/tlaplus/blob/master/amazon/serializableSnapshotIsolation.tla">Serializable snapshot isolation (Cahill et al., 2010)</a> | Michael J. Cahill, Uwe Röhm, Alan D. Fekete |  | &#10004; | FinSet, Int, Seq | 
| 49 | spanning | <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/spanning">Spanning tree broadcast algorithm in Attiya and Welch’s book</a> | Thanh Hai Tran, Igor Konnov, Josef Widder |  | &#10004; | Int | 
| 50 | SpecifyingSystems | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/SpecifyingSystems">Examples to accompany the book Specifying Systems (Lamport, 2002)</a> |  |  | &#10004; | all modules | 
| 51 | Stones | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/Stones">The same proble as CarTalkPuzzle</a> |  |  | &#10004; | FinSet, Int, Seq | 
| 52 | sums_even | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/sums_even">Two proofs for showing that x+x is even, for any natural number x.</a> |  | &#10004; | &#10004; | Int | 
| 53 | SyncConsensus | <a href="https://github.com/muratdem/PlusCal-examples/tree/master/SyncConsensus">Synchronized round consensus algorithm (Demirbas)</a> | Murat Demirbas |  | &#10004; | FinSet, Int, Seq | 
| 54 | Termination | <a href="https://github.com/nano-o/Distributed-termination-detection">Channel counting algorithm (Mattern, 1987)</a> | Giuliano Losa |  | &#10004; | FinSet, Bags, Nat | 
| 55 | Tla-tortoise-hare | <a href="https://github.com/lorin/tla-tortoise-hare">Robert Floyd's cycle detection algorithm</a> | Lorin Hochstein |  | &#10004; | Nat | 
| 56 | tower_of_hanoi | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/tower_of_hanoi">The well-known Towers of Hanoi puzzle.</a> |  |  | &#10004; | FinSet, Nat, Bit | 
| 57 | transaction_commit | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/transaction_commit">Consensus on transaction commit (Gray & Lamport, 2006)</a> | Vasily Kuznetsov, Markus Alexander Kuppe |  | &#10004; | Int | 
| 58 | TransitiveClosure | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/TransitiveClosure">The transitive closure of a relation</a> |  |  | &#10004; | FinSet, Int, Seq | 
| 59 | TwoPhase | <a href="https://github.com/tlaplus/Examples/tree/master/specifications/TwoPhase">Two-phase handshaking</a> | Stephan Merz |  | &#10004; | Nat | 
| 60 | VoldemortKV | <a href="https://github.com/muratdem/PlusCal-examples/tree/master/VoldemortKV">Voldemort distributed key value store</a> | Murat Demirbas |  | &#10004; | FinSet, Int, Seq | 


## License
Every benchmark has initially the MIT license. However, if the authors want to change the license, we can create a new license.  


## Support or Contact

Do you have any questions? Please contact <a href="mailto: tran@forsyte.ac.at">Thanh-Hai Tran</a>.
