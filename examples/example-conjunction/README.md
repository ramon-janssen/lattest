# Testing with conjunction

This is an example of testing a specification which contains conjunctive composition. Specifically, this specification is the alternating interface
automaton sG, taken from:

- [_Ramon Janssen_, Refinement and partiality for model-based testing (Doctoral dissertation), 2022, Chapter 4.3.1](https://repository.ubn.ru.nl/bitstream/handle/2066/285020/285020.pdf).

This is implementation represents a vending machine, which outputs coffee (C) and tea (T), optionally with milk (CM or TM).

# Instructions

To run the example:

- install maven and haskell stack.
- Open a terminal, go to the 'sut' folder, and run the system under test:
    - $ mvn install
    - $ mvn exec:java
- In another terminal (tab), go to the main folder of this example, and run the tester:
    - $ stack build
    - $ stack run
- The tester should now automatically connect and start testing against the system under test, and print the test results.
- To test correct or incorrect variants of the sut, in the 'sut' folder:
    - Correct sut (default): $ mvn exec:java -Dexec.args="Correct"
    - Incorrect sut that sometimes gives tea without milk: $ mvn exec:java -Dexec.args="IncorrectOutput"
    - Incorrect sut that sometimes forgets to give tea: $ mvn exec:java -Dexec.args="IncorrectTimeout"

Note, this has been tested only for linux and macOS. If you're lucky, it might just work in Windows as well (bash terminal, powershell, cygwin, cmd-prompt, I have no clue. If you do, please let me know.)
