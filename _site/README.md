
## Welcome to TLA<sup>+</sup> Benchmarks 

The page **TLA<sup>+</sup> Benchmarks** is a library of TLA<sup>+</sup> specifications for distributed algorithms. The webpage supplies the TLA<sup>+</sup> community with:

- A comprehensive library of the TLA<sup>+</sup> specifications that are available today, in order to provide an overview of how to specify an algorithm in TLA<sup>+</sup>.
- A comprehensive list of references and other interesting information for each problem.

We encourage the submission of new challenging TLA<sup>+</sup> benchmarks.

### List of benchmarks

| Name 												| Short description 																			| Failures 			| Thresholds 									| Properties 																										|
| --------------------------- | ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| <a href="http://list.cs.northwestern.edu/802.16/">802.16</a> | <a href="https://ieeexplore.ieee.org/document/5062485/">IEEE 802.16 WiMAX Protocols</a> <br/> <a href="https://www.cs.northwestern.edu/~ychen/Papers/npsec06.pdf"> Checking of 802.16 throung TLA</a> | | retry < NUM * 3 | deadlock, correctness |
| aba-asyn-byzagreement0			|	Asynchronous Byzantine agreement												| Byzantine			|	N > 3 * T, T >= F >= 0			| unforgeability, correctness, agreement												|
| <a href="https://members.loria.fr/SMerz/talks/argentina2005/Charpentier/charpov/Teaching/CS-986/TLC/">acp-sb</a> | <a href="https://dl.acm.org/citation.cfm?id=302436">Non-blocking atomic commitment</a> with a simple broadcast | clean crashes | &forall; j &isin; participants  | AC1-AC4, no recovery |
| Assignment									| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| ast													| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| async-comm									| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| bcastByz										| Asynchronous reliable broadcast													| Byzantine			| N >= 3 * T, T >= F >= 0			| unforgeability, correctness, relay														|
| bcastFolklore								| Folklore reliable broadcast															| clean crashes	| N > 1												| unforgeability, correctness, relay         										|
| bosco												| One-Step Byzantine asynchronous consensus								|	Byzantine			| N > 3T or N > 5T or N > 7T 	|	------------------------------------------------------------- |
| Boulangerie									| A variant of the bakery algorithm         							| ------------- | --------------------------- | ------------------------------------------------------------- |
| c1cs												| Consensus in one communication step											| clean crashes	| N > 3 * T										| ------------------------------------------------------------- |
| caesar4											| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| cbc_max											| Condition-based consensus																| Byzantine			| N > 2 * T, T >= F >= 0			| validity, agreement, termination															|
| cf1s-folklore-onestep				| One-step consensus																			| crashes				| N > 3 * T										| ------------------------------------------------------------- |
| Chang-Roberts								| Leader election in a ring							                  | ------------- | --------------------------- | ------------------------------------------------------------- |
| DataPort										| Dataport protocal 505.89PT															| ------------- | --------------------------- | ------------------------------------------------------------- |
| dijkstra-mutex							| Dijkstra's mutual exclusion algorithm	 							    | ------------- | --------------------------- | ------------------------------------------------------------- |	
| diskpaxos										| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| DoRiS												| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |	
| egalitarian-paxos						| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| ewd840											| Detecting distributed termination								 			  | ------------- | --------------------------- | ------------------------------------------------------------- |
| detector_chan96							| Eventually perfect failure detector											| clean crashes	|	---------------------------	| strong completeness, eventual strong accuracy									|
| fastpaxos										| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| fpaxos											| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| lamport_mutex 							| Lamport's mutual-exclusion							 								| ------------- | --------------------------- | ------------------------------------------------------------- |
| l1													| data center network L1 switch protocol, only PDF files	| ------------- | --------------------------- | ------------------------------------------------------------- |
| leaderless									| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| LongLivedAssignment					| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| losa_ap											| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| losa_rda										| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| m2paxos1										| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| m2paxos2										| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| naiad												| Naiad clock protocol, only PDF files 								 		| ------------- | --------------------------- | ------------------------------------------------------------- |
| nbacc-asyn-ray97-clean			| Asynchronous non-blocking atomic commit									| clean crashes	| N > 1												|	validity, non-triviality, termination													|
| nbacg-asyn-guer01-clean			| Asynchronous non-blocking atomic commit									| clean crashes	| N > 1												| ------------------------------------------------------------- |
| nfc04												| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| paxos												| Paxos consensus algorithm								 								| ------------- | --------------------------- | ------------------------------------------------------------- |
| raft												| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| transaction_commit					| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| TwoPhase										| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| ufd5												| ------------------------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |

### Support or Contact

Do you have any questions? Please contact  <a href="mailto: tran@forsyte.ac.at">Thanh-Hai Tran</a>.
