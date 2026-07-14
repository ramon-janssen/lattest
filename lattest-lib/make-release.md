- Check the changelog, increment version number, check version bounds on dependencies, etc.

# HACKAGE:
- Make an updated lattest-lib.cabal (e.g. by invoking stack)
- cabal sdist
- upload a package candidate
- cabal v2-haddock --builddir="$dir" --haddock-for-hackage --enable-doc
- upload the generated docs to the package candidate (under 'mainain')
- if all looks good, click 'publish'

# STACKAGE:
- todo
