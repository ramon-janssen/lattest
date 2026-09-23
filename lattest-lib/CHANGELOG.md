# Changelog for `lattest-lib`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## Unreleased
- Refactored the STS expression language, adding support for sets, lists, sum and product types and making the language more strongly typed.
  This slightly changes the interface, but STSs that were already correct should only need minimal changes.
- Added support for offline testing: Generating test sequences or trees without an adapter.
- Added the option to read and write some STS automata from and to JSON.
  This is currently aimed specifically for the integration between lattest and PICKLES,
  which is most noticable in the printing of guards and assertions (giving the ID of the corresponding guard/assertion in the input JSON).
  Please get in touch if you have other usecases!
- Added combinators to sequentially compose automata.
- Added symbolic look-ahead, which computes the combined guard of a trace through an STS.

## 0.1.1 - 2026-07-15
Bugfix patch: adds instance OrdTraversable FreeLattice, and properly kills the reading thread before its socket is closed.

## 0.1.0.0 - 2026-07-14
First release

