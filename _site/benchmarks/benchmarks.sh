#!/bin/bash

if [ ! -e 2PCwithBTM ]; then
  mkdir  2PCwithBTM
  cd  2PCwithBTM
  echo -e "#### 2PCwithBTM\n- Specification's authors: Murat Demirbas\n- Original paper: <a href="http://lamport.azurewebsites.net/tla/two-phase.html">Gray, Jim, and Leslie Lamport. "Consensus on transaction commit." ACM Transactions on Database Systems (TODS) 31.1 (2006): 133-160.</a>\n- Extended modules: FinSet, Int, Seq\n- Computation models: no faults\n- Some properties checked with TLC: consistency, NotCommitted\n\n" > README.md
  cd .. 
fi

if [ ! -e 802.16 ]; then
  mkdir  802.16
  cd  802.16
  echo -e "#### 802.16\n- Specification's authors: Prasad Narayana, Ruiming Chen, Yao Zhao, Yan Chen, Zhi (Judy) Fu, and Hai Zhou\n- Original paper: <a href="https://ieeexplore.ieee.org/document/5062485/">802.16-2009 - IEEE Standard for Local and metropolitan area networks Part 16: Air Interface for Broadband Wireless Access Systems</a>\n- Extended modules: Int, Seq, FinSet\n- Computation models: no faults\n- Some properties checked with TLC: DoS vulnerability\n\n" > README.md
  cd .. 
fi

if [ ! -e aba-asyn-byz ]; then
  mkdir  aba-asyn-byz
  cd  aba-asyn-byz
  echo -e "#### aba-asyn-byz\n- Specification's authors: Thanh Hai Tran, Igor Konnov, Josef Widder\n- Original paper: <a href="https://dl.acm.org/citation.cfm?id=214134">Bracha, Gabriel, and Sam Toueg. "Asynchronous consensus and broadcast protocols." Journal of the ACM (JACM) 32.4 (1985): 824-840.</a>\n- Extended modules: Nat\n- Computation models: Byzantine\n- Some properties checked with TLC: correctness, agreement, unforgeability\n\n" > README.md
  cd .. 
fi

if [ ! -e acp-nb ]; then
  mkdir  acp-nb
  cd  acp-nb
  echo -e "#### acp-nb\n- Specification's authors: Stephan Merz\n- Original paper: <a href="https://dl.acm.org/citation.cfm?id=302436">Babaoğlu, Özalp, and Sam Toueg. "Non-blocking atomic commitment." Distributed systems (2nd Ed.). ACM Press/Addison-Wesley Publishing Co., 1993.</a>\n- Extended modules: default theories\n- Computation models: clean crashes\n- Some properties checked with TLC: AC1-AC5, termination, AllAbort, AllCommit\n\n" > README.md
  cd .. 
fi

if [ ! -e acp-nb-wrong ]; then
  mkdir  acp-nb-wrong
  cd  acp-nb-wrong
  echo -e "#### acp-nb-wrong\n- Specification's authors: Stephan Merz\n- Original paper: <a href="https://dl.acm.org/citation.cfm?id=302436">Babaoğlu, Özalp, and Sam Toueg. "Non-blocking atomic commitment." Distributed systems (2nd Ed.). ACM Press/Addison-Wesley Publishing Co., 1993.</a>\n- Extended modules: default theories\n- Computation models: clean crashes\n- Some properties checked with TLC: AC1-AC5, termination, AllAbort, AllCommit\n\n" > README.md
  cd .. 
fi

if [ ! -e acp-sb ]; then
  mkdir  acp-sb
  cd  acp-sb
  echo -e "#### acp-sb\n- Specification's authors: Stephan Merz\n- Original paper: <a href="https://dl.acm.org/citation.cfm?id=302436">Babaoğlu, Özalp, and Sam Toueg. "Non-blocking atomic commitment." Distributed systems (2nd Ed.). ACM Press/Addison-Wesley Publishing Co., 1993.</a>\n- Extended modules: default theories\n- Computation models: clean crashes\n- Some properties checked with TLC: AC1-AC5, no recovery, termincation\n\n" > README.md
  cd .. 
fi

if [ ! -e allocator ]; then
  mkdir  allocator
  cd  allocator
  echo -e "#### allocator\n- Specification's authors: Stephan Merz\n- Original paper: <a href=""></a>\n- Extended modules: FinSet\n- Computation models: no faults\n- Some properties checked with TLC: ClientsWillReturn, ClientWillObtain\n\n" > README.md
  cd .. 
fi

if [ ! -e async-comm ]; then
  mkdir  async-comm
  cd  async-comm
  echo -e "#### async-comm\n- Specification's authors: Florent Chevrou, Aurélie Hurault, Philippe Quéinnec\n- Original paper: <a href="https://link.springer.com/article/10.1007/s00165-016-0379-x">Chevrou, Florent, Aurélie Hurault, and Philippe Quéinnec. "On the diversity of asynchronous communication." Formal Aspects of Computing 28.5 (2016): 847-879.</a>\n- Extended modules: Nat\n- Computation models: no faults\n- Some properties checked with TLC: compatibility, termination\n\n" > README.md
  cd .. 
fi

if [ ! -e bcastByz ]; then
  mkdir  bcastByz
  cd  bcastByz
  echo -e "#### bcastByz\n- Specification's authors: Thanh Hai Tran, Igor Konnov, Josef Widder\n- Original paper: <a href="https://link.springer.com/article/10.1007/BF01667080">Srikanth, T. K., and Sam Toueg. "Simulating authenticated broadcasts to derive simple fault-tolerant algorithms." Distributed Computing 2.2 (1987): 80-94.</a>\n- Extended modules: Nat, FinSet\n- Computation models: Byzantine\n- Some properties checked with TLC: correctness, relay, unforgeability\n- TLAPS proofs: unforgeability\n" > README.md
  cd .. 
fi

if [ ! -e bcastFolklore ]; then
  mkdir  bcastFolklore
  cd  bcastFolklore
  echo -e "#### bcastFolklore\n- Specification's authors: Thanh Hai Tran, Igor Konnov, Josef Widder\n- Original paper: <a href="https://dl.acm.org/citation.cfm?id=226647">Tushar Deepak Chandra and Sam Toueg. 1996. Unreliable failure detectors for reliable distributed systems. J. ACM 43, 2 (March 1996), 225-267.</a>\n- Extended modules: Nat\n- Computation models: clean crashes\n- Some properties checked with TLC: correctness, relay, unforgeability\n- TLAPS proofs: the implementation of the specification Alternative\n" > README.md
  cd .. 
fi

if [ ! -e bosco ]; then
  mkdir  bosco
  cd  bosco
  echo -e "#### bosco\n- Specification's authors: Thanh Hai Tran, Igor Konnov, Josef Widder\n- Original paper: <a href="https://link.springer.com/chapter/10.1007/978-3-540-87779-0_30">Song, Yee Jiun, and Robbert van Renesse. "Bosco: One-step byzantine asynchronous consensus." International Symposium on Distributed Computing. Springer, Berlin, Heidelberg, 2008.</a>\n- Extended modules: Nat, FinSet\n- Computation models: Byzantine\n- Some properties checked with TLC: Lemma3, Lemma4, OneStep0, OneStep1\n\n" > README.md
  cd .. 
fi

if [ ! -e Boulangerie ]; then
  mkdir  Boulangerie
  cd  Boulangerie
  echo -e "#### Boulangerie\n- Specification's authors: Stephan Merz\n- Original paper: <a href="https://dl.acm.org/citation.cfm?id=2950394">Moses, Yoram, and Katia Patkin. "Under the hood of the bakery algorithm: Mutual exclusion as a matter of priority." International Colloquium on Structural Information and Communication Complexity. Springer, Cham, 2015.</a>\n- Extended modules: Int\n- Computation models: no faults\n- Some properties checked with TLC: mutex\n- TLAPS proofs: mutual exclusion\n" > README.md
  cd .. 
fi

if [ ! -e byihive ]; then
  mkdir  byihive
  cd  byihive
  echo -e "#### byihive\n- Specification's authors: Santhosh Raju\n- Original paper: <a href="https://tools.ietf.org/rfc/rfc3506.txt">Requirements and Design for Voucher Trading System (VTS)</a>\n- Extended modules: default theories\n- Computation models: ❓\n- Some properties checked with TLC: consistency\n\n" > README.md
  cd .. 
fi

if [ ! -e byzpaxos ]; then
  mkdir  byzpaxos
  cd  byzpaxos
  echo -e "#### byzpaxos\n- Specification's authors: Leslie Lamport?\n- Original paper: <a href="http://lamport.azurewebsites.net/tla/byzsimple.pdf">Lamport, Leslie. "Byzantizing Paxos by refinement." International Symposium on Distributed Computing. Springer, Berlin, Heidelberg, 2011.</a>\n- Extended modules: Int, FinSet\n- Computation models: Byzantine\n- Some properties checked with TLC: Safety\n\n" > README.md
  cd .. 
fi

if [ ! -e c1cs ]; then
  mkdir  c1cs
  cd  c1cs
  echo -e "#### c1cs\n- Specification's authors: Thanh Hai Tran, Igor Konnov, Josef Widder\n- Original paper: <a href="https://link.springer.com/chapter/10.1007/3-540-44743-1_4">Brasileiro, Francisco, et al. "Consensus in one communication step." International Conference on Parallel Computing Technologies. Springer, Berlin, Heidelberg, 2001.</a>\n- Extended modules: Int, FinSet\n- Computation models: clean crashes\n- Some properties checked with TLC: validity, agreement, weak-agreement, termination\n\n" > README.md
  cd .. 
fi

if [ ! -e Caesar ]; then
  mkdir  Caesar
  cd  Caesar
  echo -e "#### Caesar\n- Specification's authors: Giuliano Losa\n- Original paper: <a href="https://ieeexplore.ieee.org/document/8023110/">Arun, Balaji, et al. "Speeding up Consensus by Chasing Fast Decisions." 2017 47th Annual IEEE/IFIP International Conference on Dependable Systems and Networks (DSN). IEEE, 2017.</a>\n- Extended modules: FinSet, Seq, Int\n- Computation models: clean crashes\n- Some properties checked with TLC: GraphInvariant, agreement\n\n" > README.md
  cd .. 
fi

if [ ! -e CarTalkPuzzle ]; then
  mkdir  CarTalkPuzzle
  cd  CarTalkPuzzle
  echo -e "#### CarTalkPuzzle\n- Specification's authors: \n- Original paper: <a href=""></a>\n- Extended modules: Int\n- Computation models: no faults\n- Some properties checked with TLC: ExpandSolution\n\n" > README.md
  cd .. 
fi

if [ ! -e CASPaxos ]; then
  mkdir  CASPaxos
  cd  CASPaxos
  echo -e "#### CASPaxos\n- Specification's authors: Tobias Schottdorf\n- Original paper: <a href="http://rystsov.info/2017/02/15/simple-consensus.html">In search of a simple consensus algorithm</a>\n- Extended modules: Int, FinSet\n- Computation models: crashes, lost messages\n- Some properties checked with TLC: correctness\n\n" > README.md
  cd .. 
fi

if [ ! -e cbc_max ]; then
  mkdir  cbc_max
  cd  cbc_max
  echo -e "#### cbc_max\n- Specification's authors: Thanh Hai Tran, Igor Konnov, Josef Widder\n- Original paper: <a href="https://ieeexplore.ieee.org/document/1209964/">Mostéfaoui, Achour, et al. Evaluating the condition-based approach to solve consensus. IEEE, 2003.</a>\n- Extended modules: Int, FinSet\n- Computation models: Byzantine\n- Some properties checked with TLC: validity, agreement, termination\n\n" > README.md
  cd .. 
fi

if [ ! -e cf1s-folklore ]; then
  mkdir  cf1s-folklore
  cd  cf1s-folklore
  echo -e "#### cf1s-folklore\n- Specification's authors: Thanh Hai Tran, Igor Konnov, Josef Widder\n- Original paper: <a href="https://ieeexplore.ieee.org/abstract/document/1633503/">D. Dobre and Neeraj Suri, "One-step Consensus with Zero-Degradation," International Conference on Dependable Systems and Networks (DSN'06), Philadelphia, PA, 2006, pp. 137-146.</a>\n- Extended modules: Nat\n- Computation models: clean crashes\n- Some properties checked with TLC: OneStep0, OneStep1\n\n" > README.md
  cd .. 
fi

if [ ! -e ChangRoberts ]; then
  mkdir  ChangRoberts
  cd  ChangRoberts
  echo -e "#### ChangRoberts\n- Specification's authors: Stephan Merz\n- Original paper: <a href="https://dl.acm.org/citation.cfm?id=359108">Chang, Ernest, and Rosemary Roberts. "An improved algorithm for decentralized extrema-finding in circular configurations of processes." Communications of the ACM 22.5 (1979): 281-283.</a>\n- Extended modules: Nat, Seq\n- Computation models: no faults\n- Some properties checked with TLC: termination\n\n" > README.md
  cd .. 
fi

if [ ! -e DataPort ]; then
  mkdir  DataPort
  cd  DataPort
  echo -e "#### DataPort\n- Specification's authors: Geoffrey Biggs, Noriaki Ando\n- Original paper: <a href="https://ieeexplore.ieee.org/iel7/7858577/7862346/07862411.pdf">Biggs, Geoffrey, and Noriaki Ando. "A formal specification of the RT-Middleware data transfer protocol." Simulation, Modeling, and Programming for Autonomous Robots (SIMPAR), IEEE International Conference on. IEEE, 2016.</a>\n- Extended modules: Int, Seq\n- Computation models: no faults\n- Some properties checked with TLC: deadlock\n\n" > README.md
  cd .. 
fi

if [ ! -e detector_chan96 ]; then
  mkdir  detector_chan96
  cd  detector_chan96
  echo -e "#### detector_chan96\n- Specification's authors: Thanh Hai Tran, Igor Konnov, Josef Widder\n- Original paper: <a href="https://dl.acm.org/citation.cfm?id=226647">Tushar Deepak Chandra and Sam Toueg. 1996. Unreliable failure detectors for reliable distributed systems. J. ACM 43, 2 (March 1996), 225-267. </a>\n- Extended modules: Int, FinSet\n- Computation models: clean crashes\n- Some properties checked with TLC: strong completeness, eventual strong accuracy\n\n" > README.md
  cd .. 
fi

if [ ! -e DieHard ]; then
  mkdir  DieHard
  cd  DieHard
  echo -e "#### DieHard\n- Specification's authors: \n- Original paper: <a href=""></a>\n- Extended modules: Nat\n- Computation models: no faults\n- Some properties checked with TLC: termination, TypeOK\n\n" > README.md
  cd .. 
fi

if [ ! -e dijkstra-mutex ]; then
  mkdir  dijkstra-mutex
  cd  dijkstra-mutex
  echo -e "#### dijkstra-mutex\n- Specification's authors: Markus Alexander Kuppe\n- Original paper: <a href="https://dl.acm.org/citation.cfm?id=365617">E. W. Dijkstra. 1965. Solution of a problem in concurrent programming control. Commun. ACM 8, 9 (September 1965), 569-. </a>\n- Extended modules: Int\n- Computation models: no faults\n- Some properties checked with TLC: mutex, starvation, termination\n\n" > README.md
  cd .. 
fi

if [ ! -e diskpaxos ]; then
  mkdir  diskpaxos
  cd  diskpaxos
  echo -e "#### diskpaxos\n- Specification's authors: Giuliano Losa\n- Original paper: <a href="https://lamport.azurewebsites.net/pubs/disk-paxos.pdf">Gafni, Eli, and Leslie Lamport. "Disk paxos." Distributed Computing 16.1 (2003): 1-20.</a>\n- Extended modules: Int\n- Computation models: crashes, inaccessibility\n- Some properties checked with TLC: SynodSpec\n\n" > README.md
  cd .. 
fi

if [ ! -e egalitarian-paxos ]; then
  mkdir  egalitarian-paxos
  cd  egalitarian-paxos
  echo -e "#### egalitarian-paxos\n- Specification's authors: Iulian Moraru\n- Original paper: <a href="https://dl.acm.org/citation.cfm?id=2517350">Iulian Moraru, David G. Andersen, and Michael Kaminsky. 2013. There is more consensus in Egalitarian parliaments. In Proceedings of the Twenty-Fourth ACM Symposium on Operating Systems Principles (SOSP '13). ACM, New York, NY, USA, 358-372.</a>\n- Extended modules: Nat, FinSet\n- Computation models: crashes\n- Some properties checked with TLC: nontriviality, stability, consistency\n\n" > README.md
  cd .. 
fi

if [ ! -e ewd840 ]; then
  mkdir  ewd840
  cd  ewd840
  echo -e "#### ewd840\n- Specification's authors: Stephan Merz\n- Original paper: <a href="https://www.cs.utexas.edu/users/EWD/ewd08xx/EWD840.PDF">Dijkstra, Edsger W., Wim HJ Feijen, and A_J M. Van Gasteren. "Derivation of a termination detection algorithm for distributed computations." Control Flow and Data Flow: concepts of distributed programming. Springer, Berlin, Heidelberg, 1986. 507-512.</a>\n- Extended modules: Nat\n- Computation models: no faults\n- Some properties checked with TLC: termination\n- TLAPS proofs:  type correctness, the main safety property\n" > README.md
  cd .. 
fi

if [ ! -e fastpaxos ]; then
  mkdir  fastpaxos
  cd  fastpaxos
  echo -e "#### fastpaxos\n- Specification's authors: Heidi Howard\n- Original paper: <a href="https://www.microsoft.com/en-us/research/publication/fast-paxos/">Lamport, Leslie. "Fast paxos." Distributed Computing 19.2 (2006): 79-103.</a>\n- Extended modules: Nat, FinSet\n- Computation models: crashes, lost/duplicated messages\n- Some properties checked with TLC: nontriviality, consistency\n\n" > README.md
  cd .. 
fi

if [ ! -e fpaxos ]; then
  mkdir  fpaxos
  cd  fpaxos
  echo -e "#### fpaxos\n- Specification's authors: Heidi Howard\n- Original paper: <a href="http://drops.dagstuhl.de/opus/volltexte/2017/7111/pdf/lipics-vol70-opodis2016-complete.pdf#page=361">Howard, Heidi, Dahlia Malkhi, and Alexander Spiegelman. "Flexible Paxos: Quorum Intersection Revisited." 20th International Conference on Principles of Distributed Systems. 2017.</a>\n- Extended modules: Int\n- Computation models: crashes, lost/duplicated messages\n- Some properties checked with TLC: agreed, SafeValue\n\n" > README.md
  cd .. 
fi

if [ ! -e HLC ]; then
  mkdir  HLC
  cd  HLC
  echo -e "#### HLC\n- Specification's authors: Murat Demirbas\n- Original paper: <a href="https://cse.buffalo.edu/tech-reports/2014-04.pdf">Demirbas, Murat, et al. "Logical Physical Clocks and Consistent Snapshots in Globally Distributed Databases." (2014).</a>\n- Extended modules: Int\n- Computation models: no faults\n- Some properties checked with TLC: termination, Boundedl, Boundedc, Sync\n\n" > README.md
  cd .. 
fi

if [ ! -e L1 ]; then
  mkdir  L1
  cd  L1
  echo -e "#### L1\n- Specification's authors: Tom Rodeheffer\n- Original paper: <a href="https://www.microsoft.com/en-us/research/publication/the-data-center-network-l1-switch-protocol/">C. Thacker, A. Nowatzyk, T. Rodeheffer, and F. Yu. A data center network using
FPGAs (v4.5), April 2011. Unpublished.</a>\n- Extended modules: FinSet, Nat, Seq\n- Computation models: ❓\n- Some properties checked with TLC: AllLinkEvQuiet, AllNodeInSlotEvAvail, AllNodeOutSlotEvAvail\n\n" > README.md
  cd .. 
fi

if [ ! -e lamport_mutex ]; then
  mkdir  lamport_mutex
  cd  lamport_mutex
  echo -e "#### lamport_mutex\n- Specification's authors: Stephan Merz\n- Original paper: <a href="https://lamport.azurewebsites.net/pubs/time-clocks.pdf">Lamport, Leslie. "Time, clocks, and the ordering of events in a distributed system." Communications of the ACM 21.7 (1978): 558-565.</a>\n- Extended modules: Nat, Seq\n- Computation models: no faults\n- Some properties checked with TLC: mutex\n- TLAPS proofs: mutual exclusion\n" > README.md
  cd .. 
fi

if [ ! -e leaderless ]; then
  mkdir  leaderless
  cd  leaderless
  echo -e "#### leaderless\n- Specification's authors: Giuliano Losa\n- Original paper: <a href="https://www.ssrg.ece.vt.edu/papers/2016_podc.pdf">Losa, Giuliano, Sebastiano Peluso, and Binoy Ravindran. "Brief announcement: A family of leaderless generalized-consensus algorithms." Proceedings of the 2016 ACM Symposium on Principles of Distributed Computing. ACM, 2016.</a>\n- Extended modules: FinSet, Int, Seq\n- Computation models: clean crashes\n- Some properties checked with TLC: nontriviality, consistency, stability\n\n" > README.md
  cd .. 
fi

if [ ! -e losa_ap ]; then
  mkdir  losa_ap
  cd  losa_ap
  echo -e "#### losa_ap\n- Specification's authors: Giuliano Losa\n- Original paper: <a href="https://dl.acm.org/citation.cfm?id=3154303">Carole Delporte-Gallet, Hugues Fauconnier, Eli Gafni, and Giuliano Losa. 2018. The Assignment Problem. In Proceedings of the 19th International Conference on Distributed Computing and Networking (ICDCN '18). ACM, New York, NY, USA, Article 14, 9 pages.</a>\n- Extended modules: FinSet, Nat, Seq\n- Computation models: crashes\n- Some properties checked with TLC: fairness, consistency, correctness, termination\n\n" > README.md
  cd .. 
fi

if [ ! -e losa_rda ]; then
  mkdir  losa_rda
  cd  losa_rda
  echo -e "#### losa_rda\n- Specification's authors: Giuliano Losa\n- Original paper: <a href="https://www.losa.fr/Thesis.pdf">Losa, Giuliano. Modularity in the design of robust distributed algorithms. Diss. Ph. D. thesis, Ecole Polytechnique Federale de Lausanne, 2014.</a>\n- Extended modules: FinSet, Nat, Seq\n- Computation models: crashes, lost messages\n- Some properties checked with TLC: correctness, refinement mapping\n\n" > README.md
  cd .. 
fi

if [ ! -e m2paxos ]; then
  mkdir  m2paxos
  cd  m2paxos
  echo -e "#### m2paxos\n- Specification's authors: Giuliano Losa\n- Original paper: <a href="https://ieeexplore.ieee.org/document/7579738/">Peluso, Sebastiano, et al. "Making fast consensus generally faster." Dependable Systems and Networks (DSN), 2016 46th Annual IEEE/IFIP International Conference on. IEEE, 2016.</a>\n- Extended modules: Int, Seq, FinSet\n- Computation models: clean crashes\n- Some properties checked with TLC: correctness\n\n" > README.md
  cd .. 
fi

if [ ! -e mongo-repl-tla ]; then
  mkdir  mongo-repl-tla
  cd  mongo-repl-tla
  echo -e "#### mongo-repl-tla\n- Specification's authors: Siyuan Zhou\n- Original paper: <a href="https://raft.github.io/raft.pdf">Ongaro, Diego, and John K. Ousterhout. "In search of an understandable consensus algorithm." USENIX Annual Technical Conference. 2014.</a>\n- Extended modules: FinSet, Nat, Seq\n- Computation models: crashes, lost/duplicated messages\n- Some properties checked with TLC: NeverRollbackCommitted\n\n" > README.md
  cd .. 
fi

if [ ! -e MultiPaxos ]; then
  mkdir  MultiPaxos
  cd  MultiPaxos
  echo -e "#### MultiPaxos\n- Specification's authors: Giuliano Losa\n- Original paper: <a href="https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2005-33.pdf">Lamport, Leslie. "Generalized Consensus and Paxos." (2004).</a>\n- Extended modules: Int, FinSet\n- Computation models: crashes, lost/duplicated messages\n- Some properties checked with TLC: correctness\n\n" > README.md
  cd .. 
fi

if [ ! -e N-Queens ]; then
  mkdir  N-Queens
  cd  N-Queens
  echo -e "#### N-Queens\n- Specification's authors: Stephan Merz\n- Original paper: <a href=""></a>\n- Extended modules: Nat, Seq\n- Computation models: no faults\n- Some properties checked with TLC: NoSolution, termination, invariant\n\n" > README.md
  cd .. 
fi

if [ ! -e naiad ]; then
  mkdir  naiad
  cd  naiad
  echo -e "#### naiad\n- Specification's authors: Tom Rodeheffer\n- Original paper: <a href="https://www.microsoft.com/en-us/research/wp-content/uploads/2013/11/naiad_sosp2013.pdf">Murray, Derek G., et al. "Naiad: a timely dataflow system." Proceedings of the Twenty-Fourth ACM Symposium on Operating Systems Principles. ACM, 2013.</a>\n- Extended modules: Int, Seq, FinSet\n- Computation models: no faults\n- Some properties checked with TLC: correctness\n\n" > README.md
  cd .. 
fi

if [ ! -e nbacc_ray97 ]; then
  mkdir  nbacc_ray97
  cd  nbacc_ray97
  echo -e "#### nbacc_ray97\n- Specification's authors: Thanh Hai Tran, Igor Konnov, Josef Widder\n- Original paper: <a href="https://ieeexplore.ieee.org/document/648067/">Raynal, Michel. "A case study of agreement problems in distributed systems: non-blocking atomic commitment." High-Assurance Systems Engineering Workshop, 1997., Proceedings. IEEE, 1997.</a>\n- Extended modules: Nat, FinSet\n- Computation models: clean crashes\n- Some properties checked with TLC: validity, nontriviality, termination\n\n" > README.md
  cd .. 
fi

if [ ! -e nbacg_guer01 ]; then
  mkdir  nbacg_guer01
  cd  nbacg_guer01
  echo -e "#### nbacg_guer01\n- Specification's authors: Thanh Hai Tran, Igor Konnov, Josef Widder\n- Original paper: <a href="https://dl.acm.org/citation.cfm?id=380061"></a>\n- Extended modules: Nat, FinSet\n- Computation models: clean crashes\n- Some properties checked with TLC: agreement, validity, integrity, termination\n\n" > README.md
  cd .. 
fi

if [ ! -e nfc04 ]; then
  mkdir  nfc04
  cd  nfc04
  echo -e "#### nfc04\n- Specification's authors: Steffen Zschaler\n- Original paper: <a href="https://link.springer.com/article/10.1007/s10270-009-0115-6">Zschaler, Steffen. "Formal specification of non-functional properties of component-based software systems." Software & Systems Modeling 9.2 (2010): 161-201.</a>\n- Extended modules: Real, Nat\n- Computation models: no faults\n- Some properties checked with TLC: ExecutionTimesOk, TimedCPUScheduler\n\n" > README.md
  cd .. 
fi

if [ ! -e paxos ]; then
  mkdir  paxos
  cd  paxos
  echo -e "#### paxos\n- Specification's authors: Leslie Lamport?\n- Original paper: <a href="https://lamport.azurewebsites.net/pubs/lamport-paxos.pdf">Lamport, Leslie. "The part-time parliament." ACM Transactions on Computer Systems (TOCS) 16.2 (1998): 133-169.</a>\n- Extended modules: Int, FinSet\n- Computation models: crashes, lost/duplicated messages\n- Some properties checked with TLC: TypeOK, Success\n\n" > README.md
  cd .. 
fi

if [ ! -e Prisoners ]; then
  mkdir  Prisoners
  cd  Prisoners
  echo -e "#### Prisoners\n- Specification's authors: \n- Original paper: <a href=""></a>\n- Extended modules: Nat, FinSet\n- Computation models: no faults\n- Some properties checked with TLC: Safety, Liveness\n\n" > README.md
  cd .. 
fi

if [ ! -e raft ]; then
  mkdir  raft
  cd  raft
  echo -e "#### raft\n- Specification's authors: Diego Ongaro\n- Original paper: <a href="https://raft.github.io/raft.pdf">Ongaro, Diego, and John K. Ousterhout. "In search of an understandable consensus algorithm." USENIX Annual Technical Conference. 2014.</a>\n- Extended modules: FinSet, Nat, Seq\n- Computation models: crashes, lost/duplicated messages\n- Some properties checked with TLC: deadlock\n\n" > README.md
  cd .. 
fi

if [ ! -e SnapshotIsolation ]; then
  mkdir  SnapshotIsolation
  cd  SnapshotIsolation
  echo -e "#### SnapshotIsolation\n- Specification's authors: Michael J. Cahill, Uwe Röhm, Alan D. Fekete\n- Original paper: <a href="http://cahill.net.au/wp-content/uploads/2010/02/cahill-thesis.pdf">Cahill, Michael J., Uwe Röhm, and Alan D. Fekete. "Serializable isolation for snapshot databases." ACM Transactions on Database Systems (TODS) 34.4 (2009): 20.</a>\n- Extended modules: FinSet, Int, Seq\n- Computation models: Write-rejection\n- Some properties checked with TLC: termination, correctness\n\n" > README.md
  cd .. 
fi

if [ ! -e spanning ]; then
  mkdir  spanning
  cd  spanning
  echo -e "#### spanning\n- Specification's authors: Thanh Hai Tran, Igor Konnov, Josef Widder\n- Original paper: <a href="https://github.com/banhday/tlabenchmarks/tree/master/benchmarks/spanning"></a>\n- Extended modules: Int\n- Computation models: no faults\n- Some properties checked with TLC: OneParent, termination\n\n" > README.md
  cd .. 
fi

if [ ! -e SpecifyingSystems ]; then
  mkdir  SpecifyingSystems
  cd  SpecifyingSystems
  echo -e "#### SpecifyingSystems\n- Specification's authors: \n- Original paper: <a href=""></a>\n- Extended modules: all modules\n- Computation models: \n- Some properties checked with TLC: \n\n" > README.md
  cd .. 
fi

if [ ! -e Stones ]; then
  mkdir  Stones
  cd  Stones
  echo -e "#### Stones\n- Specification's authors: \n- Original paper: <a href=""></a>\n- Extended modules: FinSet, Int, Seq\n- Computation models: no faults\n- Some properties checked with TLC: termination\n\n" > README.md
  cd .. 
fi

if [ ! -e sums_even ]; then
  mkdir  sums_even
  cd  sums_even
  echo -e "#### sums_even\n- Specification's authors: \n- Original paper: <a href=""></a>\n- Extended modules: Int\n- Computation models: no faults\n- Some properties checked with TLC: even\n- TLAPS proofs: the fact that x+x is even, for any natural number x.\n" > README.md
  cd .. 
fi

if [ ! -e SyncConsensus ]; then
  mkdir  SyncConsensus
  cd  SyncConsensus
  echo -e "#### SyncConsensus\n- Specification's authors: Murat Demirbas\n- Original paper: <a href="http://muratbuffalo.blogspot.com/2017/11/tlapluscal-modeling-of-synchronized.html">TLA+/PlusCal modeling of Synchronized Round Consensus Algorithm</a>\n- Extended modules: FinSet, Int, Seq\n- Computation models: crashes\n- Some properties checked with TLC: agreement, Syncterm, Term\n\n" > README.md
  cd .. 
fi

if [ ! -e Termination ]; then
  mkdir  Termination
  cd  Termination
  echo -e "#### Termination\n- Specification's authors: Giuliano Losa\n- Original paper: <a href="https://link.springer.com/article/10.1007/BF01782776">Mattern, Friedemann. "Algorithms for distributed termination detection." Distributed computing 2.3 (1987): 161-175.</a>\n- Extended modules: FinSet, Bags, Nat\n- Computation models: no faults\n- Some properties checked with TLC: termination\n\n" > README.md
  cd .. 
fi

if [ ! -e Tla-tortoise-hare ]; then
  mkdir  Tla-tortoise-hare
  cd  Tla-tortoise-hare
  echo -e "#### Tla-tortoise-hare\n- Specification's authors: Lorin Hochstein\n- Original paper: <a href="http://www.siafoo.net/algorithm/10">Floyd's Cycle Detection Algorithm (The Tortoise and the Hare)</a>\n- Extended modules: Nat\n- Computation models: no faults\n- Some properties checked with TLC: termination, partial correctness\n\n" > README.md
  cd .. 
fi

if [ ! -e tower_of_hanoi ]; then
  mkdir  tower_of_hanoi
  cd  tower_of_hanoi
  echo -e "#### tower_of_hanoi\n- Specification's authors: \n- Original paper: <a href=""></a>\n- Extended modules: FinSet, Nat, Bit\n- Computation models: no faults\n- Some properties checked with TLC: termination, NotSolved\n\n" > README.md
  cd .. 
fi

if [ ! -e transaction_commit ]; then
  mkdir  transaction_commit
  cd  transaction_commit
  echo -e "#### transaction_commit\n- Specification's authors: Vasily Kuznetsov, Markus Alexander Kuppe\n- Original paper: <a href="https://dl.acm.org/citation.cfm?id=1132867">Gray, Jim, and Leslie Lamport. "Consensus on transaction commit." ACM Transactions on Database Systems (TODS) 31.1 (2006): 133-160.</a>\n- Extended modules: Int\n- Computation models: crashes, lost/duplicated messages\n- Some properties checked with TLC: consistency, TypeOK\n\n" > README.md
  cd .. 
fi

if [ ! -e TransitiveClosure ]; then
  mkdir  TransitiveClosure
  cd  TransitiveClosure
  echo -e "#### TransitiveClosure\n- Specification's authors: \n- Original paper: <a href=""></a>\n- Extended modules: FinSet, Int, Seq\n- Computation models: \n- Some properties checked with TLC: \n\n" > README.md
  cd .. 
fi

if [ ! -e TwoPhase ]; then
  mkdir  TwoPhase
  cd  TwoPhase
  echo -e "#### TwoPhase\n- Specification's authors: Stephan Merz\n- Original paper: <a href="https://github.com/tlaplus/Examples/tree/master/specifications/TwoPhase">Two-phase handshaking</a>\n- Extended modules: Nat\n- Computation models: no faults\n- Some properties checked with TLC: Inv\n\n" > README.md
  cd .. 
fi

if [ ! -e VoldemortKV ]; then
  mkdir  VoldemortKV
  cd  VoldemortKV
  echo -e "#### VoldemortKV\n- Specification's authors: Murat Demirbas\n- Original paper: <a href="http://www.project-voldemort.com/voldemort/">Project Voldemort - a distributed database</a>\n- Extended modules: FinSet, Int, Seq\n- Computation models: crashes\n- Some properties checked with TLC: consistency\n\n" > README.md
  cd .. 
fi





