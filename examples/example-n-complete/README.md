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

Note, this has been tested only for linux and macOS. If you're lucky, it might just work in Windows as well (bash terminal, powershell, cygwin, cmd-prompt, I have no clue. If you do, please let me know.)
