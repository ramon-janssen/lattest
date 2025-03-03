#!/bin/bash

# stack repl --only-main
echo ":q\n" | stack repl --ghc-options "-Wno-unused-top-binds -Wno-orphans"
