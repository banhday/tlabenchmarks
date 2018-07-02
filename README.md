## Welcome to TLA<sup>+</sup> Benchmarks 

The page **TLA<sup>+</sup> Benchmarks** is a library of TLA<sup>+</sup> specifications for distributed algorithms. The webpage supplies the TLA<sup>+</sup> community with:

- A comprehensive library of the TLA<sup>+</sup> specifications that are available today, in order to provide an overview of how to specify an algorithm in TLA<sup>+</sup>.
- A comprehensive list of references and other interesting information for each problem.

We encourage the submission of new challenging TLA<sup>+</sup> benchmarks.

### List of benchmarks

| Name 												| Short description 												| Failures 			| Thresholds 									| Properties 																										|
| --------------------------- | ----------------------------------------- | ------------- | --------------------------- | ------------------------------------------------------------- |
| frb-bcast-folklore-crash		|	Folklore reliable broadcast, TACAS'08			| clean crashes	| N > 1												| unforgeability, correctness, relay, tacas08										|
| strb-bcast-byz        			| Asynchronous reliable broadcast						| Byzantine			| N >= 3 * T, T >= F >= 0			| unforgeability, correctness, relay														|
| aba-asyn-byzagreement0			|	Asynchronous Byzantine agreement					| Byzantine			|	N > 3 * T, T >= F >= 0			| unforgeability, correctness, agreement												|
| cbc-cond-consensus2					| ACondition-based consensus								| Byzantine			| N > 2 * T, T >= F >= 0			| validity, agreement, termination															|
| nbac-asyn-ray97-nbac	 			| Asynchronous non-blocking atomic commit		| crashes				| N > 1												| validity, non-triviality, termination													|	
| nbacc-asyn-ray97-nbac-clean	| Asynchronous non-blocking atomic commit		| clean crashes	| N > 1												|	validity, non-triviality, termination													|
| nbacg-asyn-guer01-nbac			| Asynchronous non-blocking atomic commit		| crashes				| N > 1												| agreement, abort_validity, commit_validity, termination				|
| cf1s-folklore-onestep				| One-step consensus												| crashes				| N > 3 * T										| one_step0, one_step1																					|
| c1cs												| Consensus in one communication step				| crashes				| N > 3 * T										| one_step0, one_step1, fast0, fast1														|	
| bosco												| One-Step Byzantine asynchronous consensus	|	Byzantine			| N > 3T or N > 5T or N > 7T |one_step0, one_step1, lemma3_0, lemma3_1, lemma4_0, lemma4_1		|

### Support or Contact

Do you have any questions? Please contact  <a href="mailto: tran@forsyte.ac.at">Thanh-Hai Tran</a>.
