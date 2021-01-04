# VODCondGen for Data-race Detections 
Using variable-oriented-DAG condition generator to generate Z3-provable variable race/race-free conditions for LLNL OpenMP data-race bench.

## Ideas
LLNL provides a data-race bench and evaluation (https://github.com/LLNL/dataracebench/wiki/Tool-Evaluation-Dashboard). And I want to provide a data-race detector solution achieving 100% accuracy combining my VOD and Microsoft Z3 (https://github.com/Z3Prover) theory proving techniques.

## Demonstrations 
As the project gets improved I will release more and more Z3 SMT2 variable condition files, which are generated by my private and unpublished Eclipse C/C++ editor plug-in project named VODCondGen, corresponding to the LLNL data-race dench files. A variable condition file proved 'sat' (satisfiable) by Z3 is said a data-race is detected on that variable. While one proved 'unsat' (unsatisfiable) is said never having a data-race. If I generate and prove condition files for all variables in an OpenMP program with either 'sat' or 'unsat' results, I can clearly say that the program is either race-prone or race-free.
